import CvxLean.Lib.Equivalence
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Arith.NormNumVariants
import CvxLean.Tactic.PreDCP.RewriteMapExt
import CvxLean.Tactic.PreDCP.RewriteMapLibrary
import CvxLean.Tactic.PreDCP.Egg.All

namespace CvxLean

open Lean Elab Meta Tactic Term IO

/-- Convert `OC` tree to `EggMinimization`. -/
def EggMinimization.ofOCTree (oc : OC (String × EggTree)) : EggMinimization :=
  { objFun := EggTree.toEggString oc.objFun.2,
    constrs := Array.data <| oc.constr.map fun (h, c) => (h, EggTree.toEggString c) }

/-- Given the rewrite name and direction from egg's output, find the appropriate
tactic in the environment. It also returns a bool to indicate if the proof needs
an intermediate equality step. Otherwise, the tactic will be applied directly.
-/
def findTactic (atObjFun : Bool) (rewriteName : String) (direction : EggRewriteDirection) :
    MetaM (TSyntax `tactic × Bool) := do
  match ← getTacticFromRewriteName rewriteName with
  | some (tac, mapObjFun) =>
    if mapObjFun then
      return (tac, true)
    else
      match direction with
      | EggRewriteDirection.Forward => return (tac, false)
      | EggRewriteDirection.Backward =>
          -- Simply flip the goal so that the rewrite is applied to the target.
          if atObjFun then
            return (← `(tactic| (rw [eq_comm]; $tac)), false)
          else
            return (← `(tactic| (rw [Iff.comm]; $tac)), false)
  | _ => throwError "Unknown rewrite name {rewriteName}({direction})."

/-- Given the rewrite index (`0` for objective function, `1` to `numConstr` for
for for constraints), return the rewrite lemma that needs to be applied. Also
return the number of arguments of each rewrite lemma to be able to build an
expression in `rewriteWrapperApplyExpr`.
TODO: Use conv tactics. -/
def rewriteWrapperLemma (rwIdx : Nat) (numConstrs : Nat) : MetaM (Name × Nat) :=
  if rwIdx == 0 then
    return (``Minimization.Equivalence.rewrite_objFun, 1)
  else if rwIdx == numConstrs then
    match rwIdx with
    | 1  => return (``Minimization.Equivalence.rewrite_constraint_1_last,  1)
    | 2  => return (``Minimization.Equivalence.rewrite_constraint_2_last,  2)
    | 3  => return (``Minimization.Equivalence.rewrite_constraint_3_last,  3)
    | 4  => return (``Minimization.Equivalence.rewrite_constraint_4_last,  4)
    | 5  => return (``Minimization.Equivalence.rewrite_constraint_5_last,  5)
    | 6  => return (``Minimization.Equivalence.rewrite_constraint_6_last,  6)
    | 7  => return (``Minimization.Equivalence.rewrite_constraint_7_last,  7)
    | 8  => return (``Minimization.Equivalence.rewrite_constraint_8_last,  8)
    | 9  => return (``Minimization.Equivalence.rewrite_constraint_9_last,  9)
    | 10 => return (``Minimization.Equivalence.rewrite_constraint_10_last, 10)
    | _  => throwError "`pre_dcp` error: can only rewrite problems with up to 10 constraints."
  else
    match rwIdx with
    | 1  => return (``Minimization.Equivalence.rewrite_constraint_1,  1)
    | 2  => return (``Minimization.Equivalence.rewrite_constraint_2,  2)
    | 3  => return (``Minimization.Equivalence.rewrite_constraint_3,  3)
    | 4  => return (``Minimization.Equivalence.rewrite_constraint_4,  4)
    | 5  => return (``Minimization.Equivalence.rewrite_constraint_5,  5)
    | 6  => return (``Minimization.Equivalence.rewrite_constraint_6,  6)
    | 7  => return (``Minimization.Equivalence.rewrite_constraint_7,  7)
    | 8  => return (``Minimization.Equivalence.rewrite_constraint_8,  8)
    | 9  => return (``Minimization.Equivalence.rewrite_constraint_9,  9)
    | 10 => return (``Minimization.Equivalence.rewrite_constraint_10, 10)
    | _  => throwError "`pre_dcp` error: can only rewrite problems with up to 10 constraints."

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
  -- One extra argument for the objective function.
  let args ← Array.range (numArgs + 1) |>.mapM fun _ => mkFreshExprMVar none
  return mkAppN (mkConst rwName) (signature ++ args ++ #[expected])

/-- Given an egg rewrite and a current goal with all the necessary information
about the minimization problem, we find the appropriate rewrite to apply, and
output the remaining goals. -/
def evalStep (step : EggRewrite) (vars : List Name) (tagsMap : HashMap String ℕ) :
    EquivalenceBuilder := fun eqvExpr g => g.withContext do
  trace[Meta.debug] "evalStep: {g}"
  let tag ← liftMetaM <| do
    if step.location == "objFun" then
      return "objFun"
    else if let [_, tag] := step.location.splitOn ":" then
      return tag
    else
      throwError "`pre_dcp` error: Unexpected tag name {step.location}."
  let tagNum := tagsMap.find! step.location
  let atObjFun := tagNum == 0

  -- TODO: Do not handle them as exceptions, get the names of the wrapper lemmas
  -- directly.
  let (rwWrapper, numArgs) ← rewriteWrapperLemma tagNum (tagsMap.size - 1)

  -- Build expexcted expression to generate the right rewrite condition. Again,
  -- mapping the objective function is an exception where the expected term is
  -- not used.
  let expectedTermStr := step.expectedTerm
  let mut expectedExpr ← EggString.toExpr vars expectedTermStr
  if !atObjFun then
    expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
  let fvars := Array.mk <| vars.map (fun v => mkFVar (FVarId.mk v))
  -- TODO: Why do we need this???
  let D ← instantiateMVars eqvExpr.domainP
  expectedExpr ← withLocalDeclD `p D fun p => do
    Meta.withDomainLocalDecls D  p fun xs prs => do
      let replacedFVars := Expr.replaceFVars expectedExpr fvars xs
      mkLambdaFVars #[p] (Expr.replaceFVars replacedFVars xs prs)

  let (tacStx, isMap) ← findTactic atObjFun step.rewriteName step.direction

  let gToChange := ← do
    if isMap then return g else
      let toApply ← rewriteWrapperApplyExpr isMap rwWrapper numArgs expectedExpr
      let gsAfterApply ← g.apply toApply
      if gsAfterApply.length != 1 then
        trace[Meta.debug] "gsAfterApply: {gsAfterApply}."
        throwError "Expected 1 goal after applying rewrite wrapper, got {gsAfterApply.length}."

      return gsAfterApply[0]!

  trace[Meta.debug] "After apply. {gToChange}"

  -- Finally, apply the tactic that should solve all proof obligations. A mix
  -- of approaches using `norm_num` in combination with the tactic provided
  -- by the user for this particular rewrite.
  let fullTac : Syntax ← `(tactic| intros;
    try { norm_num_clean_up; $tacStx <;> norm_num_simp_pow } <;>
    try { $tacStx <;> norm_num_simp_pow } <;>
    try { norm_num_simp_pow })
  let gsAfterRw ← evalTacticAt fullTac gToChange
  trace[Meta.debug] "After tactic. {gsAfterRw}"

  if gsAfterRw.length == 0 then
    pure ()
  else
    dbg_trace s!"Failed to rewrite {step.rewriteName}."
    for g in gsAfterRw do
      dbg_trace s!"Could not prove {← Meta.ppGoal g}."
    dbg_trace s!"Tactic : {Syntax.prettyPrint fullTac}"

def preDCPBuilder : EquivalenceBuilder := fun eqvExpr g => g.withContext do
  let lhs ← eqvExpr.toMinimizationExprLHS

  -- Get optimization variables.
  let vars ← withLambdaBody lhs.constraints fun p _ => do
    let pr ← mkProjections lhs.domain p
    return pr.map (Prod.fst)
  trace[Meta.debug] "Vars: {vars}."
  let varsStr := vars.map toString

  -- Get goal as tree and create tags map.
  let (gStr, domainConstrs) ← ExtendedEggTree.fromMinimization lhs varsStr
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
  let gStr := { gStr with constr := gStr.constr.filter (fun (h, _) => !constrsToIgnore.contains h) }

  -- Prepare egg request.
  let eggMinimization := EggMinimization.ofOCTree gStr
  let eggRequest : EggRequest :=
    { domains := varDomainConstrs.data,
      target := eggMinimization }

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
    let mut g := g
    for step in steps do
      let gs ← Tactic.run g <| (evalStep step vars tagsMap).toTactic
      if gs.length != 1 then
        throwError "Failed to rewrite {step.rewriteName} after evaluating step ({gs.length} goals)."
      else
        g := gs[0]!
        dbg_trace s!"Rewrote {step.rewriteName}."

    let gsFinal ← evalTacticAt (← `(tactic| equivalence_rfl)) g
    if gsFinal.length != 0 then
      throwError "`pre_dcp` error: Could not close last goal."
  catch e =>
    let eStr ← e.toMessageData.toString
    throwError "`pre_dcp` error: {eStr}"

/-- The `pre_dcp` tactic encodes a given minimization problem, sends it to egg, and reconstructs
the proof from egg's output. -/
syntax (name := preDCP) "pre_dcp" : tactic

@[tactic preDCP]
def evalPreDCP : Tactic := fun stx => match stx with
  | `(tactic| pre_dcp) => withMainContext do
      normNumCleanUp (useSimp := false)
      preDCPBuilder.toTactic
      -- normNumCleanUp (useSimp := false)
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end CvxLean
