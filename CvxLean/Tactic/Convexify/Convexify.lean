import Lean
import CvxLean.Meta.Minimization
import CvxLean.Lib.Equivalence
import CvxLean.Tactic.Arith.NormNumVariants
import CvxLean.Tactic.Convexify.RewriteMapExt
import CvxLean.Tactic.Convexify.RewriteMapLibrary
import CvxLean.Tactic.Convexify.Egg.All

namespace CvxLean

open Lean Elab Meta Tactic Term IO

/-- Convert `OC` tree to `EggMinimization`. -/
def EggMinimization.ofOCTree (oc : OC (String × EggTree)) :
  EggMinimization :=
  { objFun := EggTree.toEggString oc.objFun.2,
    constrs := Array.data <| oc.constr.map fun (h, c) =>
      (h, EggTree.toEggString c) }

/-- Given the rewrite name and direction from egg's output, find the appropriate
tactic in the environment. It also returns a bool to indicate if the proof needs
an intermediate equality step. Otherwise, the tactic will be applied directly.
-/
def findTactic (isEquiv atObjFun : Bool) (rewriteName : String)
  (direction : EggRewriteDirection) :
  MetaM (Bool × TSyntax `tactic) := do
  match ← getTacticFromRewriteName rewriteName with
  | some (tac, mapObjFun) =>
    if mapObjFun then
      if isEquiv then
        return (true, ← `(tactic| arith))
      else
        return (false, tac)
    else
      match direction with
      | EggRewriteDirection.Forward => return (true, tac)
      | EggRewriteDirection.Backward =>
          -- Simply flip the goal so that the rewrite is applied to the target.
          if atObjFun then
            return (true, ← `(tactic| (rw [eq_comm]; $tac)))
          else
            return (true, ← `(tactic| (rw [Iff.comm]; $tac)))
  | _ => throwError "Unknown rewrite name {rewriteName}({direction})."

/-- Given the rewrite index (`0` for objective function, `1` to `numConstr` for
for for constraints), return the rewrite lemma that needs to be applied. Also
return the number of arguments of each rewrite lemma to be able to build an
expression in `rewriteWrapperApplyExpr`. -/
def rewriteWrapperLemma (rwIdx : Nat) (numConstrs : Nat) : MetaM (Name × Nat) :=
  if rwIdx == 0 then
    return (`rewrite_objective, 1)
  else if rwIdx == numConstrs then
    match rwIdx with
    | 1  => return (`rewrite_constraint_1_last,  1)
    | 2  => return (`rewrite_constraint_2_last,  2)
    | 3  => return (`rewrite_constraint_3_last,  3)
    | 4  => return (`rewrite_constraint_4_last,  4)
    | 5  => return (`rewrite_constraint_5_last,  5)
    | 6  => return (`rewrite_constraint_6_last,  6)
    | 7  => return (`rewrite_constraint_7_last,  7)
    | 8  => return (`rewrite_constraint_8_last,  8)
    | 9  => return (`rewrite_constraint_9_last,  9)
    | 10 => return (`rewrite_constraint_10_last, 10)
    | _  => throwError "convexify can only rewrite problems with up to 10 constraints."
  else
    match rwIdx with
    | 1  => return (`rewrite_constraint_1,  1)
    | 2  => return (`rewrite_constraint_2,  2)
    | 3  => return (`rewrite_constraint_3,  3)
    | 4  => return (`rewrite_constraint_4,  4)
    | 5  => return (`rewrite_constraint_5,  5)
    | 6  => return (`rewrite_constraint_6,  6)
    | 7  => return (`rewrite_constraint_7,  7)
    | 8  => return (`rewrite_constraint_8,  8)
    | 9  => return (`rewrite_constraint_9,  9)
    | 10 => return (`rewrite_constraint_10, 10)
    | _  => throwError "convexify can only rewrite problems with up to 10 constraints."

/-- -/
def rewriteWrapperApplyExpr (givenRange : Bool) (rwName : Name) (numArgs : Nat) (expected : Expr) :
  MetaM Expr := do
  -- Distinguish between lemmas that have `{D R} [Preorder R]` and those that
  -- only have `{D}` because `R` is fixed.
  let signature :=
    if givenRange then
      #[← mkFreshExprMVar none]
    else
      #[← mkFreshExprMVar none, Lean.mkConst `Real, ← mkFreshExprMVar none]
  let args ← Array.range numArgs |>.mapM fun _ => mkFreshExprMVar none
  return mkAppN (mkConst rwName) (signature ++ args ++ #[expected])

/-- Given an egg rewrite and a current goal with all the necessary information
about the minimization problem, we find the appropriate rewrite to apply, and
output the remaining goals. -/
def evalStep (g : MVarId) (step : EggRewrite)
  (vars : List Name) (fvars : Array Expr) (domain : Expr)
  (numConstrTags : ℕ) (tagsMap : HashMap String ℕ) (isEquiv : Bool) :
  TacticM (List MVarId) := withMainContext <| do
  let tag ← liftMetaM <| do
    if step.location == "objFun" then
      return "objFun"
    else if let [_, tag] := step.location.splitOn ":" then
      return tag
    else
      throwError "Unexpected tag name {step.location}."
  let tagNum := tagsMap.find! step.location
  let atObjFun := tagNum == 0

  -- Special case when mapping the objective function in equivalence mode. Note
  -- that in this case, the range is set to ℝ, whereas for other rewrites, it
  -- could be other types.
  let mapLogInEquiv := isEquiv && step.rewriteName == "map_objFun_log"
  let mapSqInEquiv := isEquiv && step.rewriteName == "map_objFun_sq"
  let mapObjFunInEquiv := mapLogInEquiv || mapSqInEquiv
  let givenRange := mapObjFunInEquiv

  -- TODO: Do not handle them as exceptions, get the names of the wrapper lemmas
  -- directly.
  let (rwWrapperRaw, numArgs) :=
    if mapLogInEquiv then
      (`map_objFun_log, 1)
    else if mapSqInEquiv then
      (`map_objFun_sq, 1)
    else
      ← rewriteWrapperLemma tagNum numConstrTags

  -- Different rewrite wrappers for equivalence and non-equivalence cases.
  let rwWrapper :=
    (if isEquiv then `MinimizationQ else `Minimization) ++ rwWrapperRaw

  -- Build expexcted expression to generate the right rewrite condition. Again,
  -- mapping the objective function is an exception where the expected term is
  -- not used.
  let expectedTermStr := step.expectedTerm
  let mut expectedExpr ← EggString.toExpr vars expectedTermStr
  if !atObjFun then
    expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
  expectedExpr ← withLocalDeclD `p domain fun p => do
    Meta.withDomainLocalDecls domain p fun xs prs => do
      let replacedFVars := Expr.replaceFVars expectedExpr fvars xs
      mkLambdaFVars #[p] (Expr.replaceFVars replacedFVars xs prs)
  if mapObjFunInEquiv then
    expectedExpr ← mkFreshExprMVar none

  let (needsEq, tacStx) ← findTactic isEquiv atObjFun step.rewriteName step.direction
  if needsEq then
    let toApply ← rewriteWrapperApplyExpr givenRange rwWrapper numArgs expectedExpr
    -- Goals after initial application of rewrite wrapper (the objective function or
    -- constraint codnition has not been solved yet).
    let mut gs := []

    if !isEquiv then
      -- In the `reduction` command, we simply apply the lemma.
      gs ← g.apply toApply
    else
      -- In the `equivalence` command, we first open a new goal by transitivty
      -- and then apply the lemma, otherwise, we would solve it immediately and
      -- the process would terminate.
      let transGs ← evalTacticAt (← `(tactic| apply Minimization.Equivalence.trans)) g;
      if transGs.length != 4 then
        throwError "Equivalence mode. Expected 4 goals after applying `trans`, got {transGs.length}."

      let gToChange := transGs[0]!
      let nextG := transGs[1]!
      nextG.setTag `sol

      let gsAfterApply ← gToChange.apply toApply

      if gsAfterApply.length != 1 then
        throwError "Equivalence mode. Expected 1 goal after applying rewrite wrapper, got {gsAfterApply.length}."

      let gToRw := gsAfterApply[0]!
      gToRw.setTag `hrw

      gs := [gToRw, nextG]

    -- Make sure the remaining goals are a proof obligation and the goal opened
    -- for the next step.
    if gs.length != 2 then
      dbg_trace s!"Failed to rewrite {step.rewriteName} after applying the wrapper lemma."
      return gs

    let gToRw := gs[0]!
    let gToRwTag ← gToRw.getTag

    if gToRwTag != `hrw then
      dbg_trace s!"Unexpected tag name {gToRwTag} (expected hrw) when rewriting {step.rewriteName}."
      return gs

    let gSol := gs[1]!
    let gSolTag ← gSol.getTag

    if gSolTag != `sol then
      dbg_trace s!"Unexpected tag name {gSolTag} (expected sol) when rewriting {step.rewriteName}."
      return gs

    gSol.setTag Name.anonymous

    -- Finally, apply the tactic that should solve all proof obligations. A mix
    -- of approaches using `norm_num` in combination with the tactic provided
    -- by the user for this particular rewrite.
    let fullTac : Syntax ← `(tactic| intros;
      try { norm_num_clean_up; $tacStx <;> norm_num_simp_pow } <;>
      try { $tacStx <;> norm_num_simp_pow } <;>
      try { norm_num_simp_pow })
    let gsAfterRw ← evalTacticAt fullTac gToRw

    if gsAfterRw.length == 0 then
      return [gSol]
    else
      dbg_trace s!"Failed to rewrite {step.rewriteName} after rewriting constraint / objective function (equiv {isEquiv})."
      for g in gs do
        dbg_trace s!"Could not prove {← Meta.ppGoal g}."
      dbg_trace s!"Tactic : {Syntax.prettyPrint fullTac}"

      return [gSol] ++ gsAfterRw
  else
    -- No equality case. This only happens under the `reduction` command, when
    -- the step involves mapping the objectiver function.
    evalTacticAt tacStx g

/-- The `convexify` tactic encodes a given minimization problem, sends it to
egg, and reconstructs the proof from egg's output. It works both under the
`reduction` and `equivalence` commands. -/
syntax (name := convexify) "convexify" : tactic

@[tactic convexify]
def evalConvexify : Tactic := fun stx => match stx with
  | `(tactic| convexify) => withMainContext <| withRef stx do
    -- Generate expression from goal. Handle cleaning up numbers, and
    -- equivalence case.
    normNumCleanUp (useSimp := false)
    let gTarget ← getMainTarget
    let isEquiv := gTarget.isAppOf ``Minimization.Equivalence
    let mut gExprRaw ← liftM <| Meta.getExprRawFromGoal isEquiv gTarget

    -- Unfold if necessary, in which case we might need to clean up numbers
    -- again.
    if let Expr.const n _ := gExprRaw then
      unfoldTarget n
      dbg_trace s!"Convexify problem name: {n}"
      normNumCleanUp (useSimp := false)
      let gTarget ← getMainTarget
      gExprRaw ← liftM <| Meta.getExprRawFromGoal isEquiv gTarget
    else
      dbg_trace s!"Convexify problem name: unknown"

    -- Get `MinmizationExpr`.
    let gExpr ← MinimizationExpr.fromExpr gExprRaw

    -- Get optimization variables.
    let vars ← withLambdaBody gExpr.constraints fun p _ => do
      let pr ← mkProjections gExpr.domain p
      return pr.map (Prod.fst)
    let varsStr := vars.map toString
    let fvars := Array.mk <| vars.map (fun v => mkFVar (FVarId.mk v))
    let domain := composeDomain <| vars.map (fun v => (v, Lean.mkConst ``Real))

    -- Get goal as tree and create tags map.
    let (gStr, domainConstrs) ← ExtendedEggTree.fromMinimization gExpr varsStr
    let numConstrTags := gStr.constr.size
    let mut tagsMap := HashMap.empty
    tagsMap := tagsMap.insert "objFun" 0
    let mut idx := 1
    for (h, _) in gStr.constr do
      tagsMap := tagsMap.insert h idx
      idx := idx + 1

    -- Handle domain constraints.
    let varDomainConstrs := domainConstrs.map (fun (_, v, d) => (v, d))
    let constrsToIgnore := domainConstrs.map (fun (h, _, _) => h)

    -- Remove domain constraints before sending it to egg.
    let gStr := { gStr with
      constr := gStr.constr.filter (fun (h, _) => !constrsToIgnore.contains h) }

    -- Prepare egg request.
    let eggMinimization := EggMinimization.ofOCTree gStr
    let eggRequest : EggRequest := {
      domains := varDomainConstrs.data,
      target := eggMinimization
    }

    try
      -- Call egg (time it for evaluation).
      let before ← BaseIO.toIO IO.monoMsNow
      let steps ← runEggRequest eggRequest
      let after ← BaseIO.toIO IO.monoMsNow
      let diff := after - before
      dbg_trace s!"Egg time: {diff} ms."
      dbg_trace s!"Number of steps: {steps.size}."
      let size := (gStr.map fun (_, t) => t.size).fold 0 Nat.add
      dbg_trace s!"Term size: {size}."
      dbg_trace s!"Term JSON: {eggMinimization.toJson}."

      -- Apply steps.
      let mut g ← getMainGoal
      for step in steps do
        let gs ← evalStep g step vars fvars domain numConstrTags tagsMap isEquiv
        if gs.length != 1 then
          dbg_trace s!"Failed to rewrite {step.rewriteName} after evaluating step ({gs.length} goals)."
          setGoals gs
          break
        else
          dbg_trace s!"Rewrote {step.rewriteName}."
          g := gs[0]!
        replaceMainGoal [g]

      let gs ← getUnsolvedGoals
      if gs.length != 1 then
        replaceMainGoal gs
        throwError "Failed to close subgoals."

      normNumCleanUp (useSimp := false)

      saveTacticInfoForToken stx
    catch e =>
      let eStr ← e.toMessageData.toString
      throwError "convexify failed with error: {eStr}"

  | _ => throwUnsupportedSyntax

end CvxLean
