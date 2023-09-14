import Lean
import Mathlib.Tactic.NormNum
import CvxLean.Lib.Equivalence
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.RewriteMapExt
import CvxLean.Tactic.PreDCP.RewriteMapLibrary
import CvxLean.Tactic.PreDCP.Egg.All

namespace CvxLean

open Lean Elab Meta Tactic Term IO

/-- -/
def EggMinimization.ofOCTree (oc : OC (String × Tree String String)) : 
  EggMinimization :=
  { objFun := EggTree.toEggString oc.objFun.2, 
    constrs := Array.data <| oc.constr.map fun (h, c) => 
      [h, EggTree.toEggString c] }

/-- Given the rewrite name and direction from egg's output, find the appropriate
tactic in the environment. It also returns a bool to indicate if the proof needs
an intermediate equality step. Otherwise, the tactic will be applied directly. -/
def findTactic (isEquiv : Bool) : String → EggRewriteDirection → Bool × MetaM (TSyntax `tactic)
  -- NOTE(RFM): Only instance of a rewriting without proving equality. It is 
  -- also the only case where only one direction is allowed.
  | "map_objFun_log", EggRewriteDirection.Forward =>
    if isEquiv then 
      (true, `(tactic| positivity))
    else 
      (false, `(tactic| map_objFun_log))
  | rewriteName, direction => (true, do
    match ← getTacticFromRewriteName rewriteName with 
    | some tac => 
      match direction with 
      | EggRewriteDirection.Forward => return tac
      | EggRewriteDirection.Backward => 
          -- Simply flip the goal so that the rewrite is applied to the target.
          `(tactic| ((first | apply Eq.symm | apply Iff.symm); $tac))
    | _ => throwError "Unknown rewrite name {rewriteName}({direction}).")

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

/-- Version of `norm_num` used to get rid of the `OfScientific`s. -/
def normNumCleanUp (useSimp : Bool) : TacticM Unit :=
  Mathlib.Meta.NormNum.elabNormNum mkNullNode mkNullNode (useSimp := useSimp)

syntax (name := norm_num_clean_up) "norm_num_clean_up" : tactic

@[tactic norm_num_clean_up]
def evalNormNumCleanUp : Tactic := fun stx => match stx with
  | `(tactic| norm_num_clean_up) => do
    normNumCleanUp (useSimp := false)
    saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

/-- -/
def evalStep (g : MVarId) (step : EggRewrite)
  (vars : List Name) (fvars : Array Expr) (domain : Expr) 
  (numConstrTags : ℕ) (tagsMap : HashMap String ℕ) (isEquiv : Bool) : 
  TacticM (List MVarId) := do
  let tag := step.location
  let tagNum := tagsMap.find! tag
  let atObjFun := tagNum == 0

  -- Special case when mapping the logarithm to the objective function in 
  -- equivalence mode. It is the only case where the range is forced to be ℝ.
  let mapLogInEquiv := isEquiv && step.rewriteName == "map_objFun_log"
  let givenRange := mapLogInEquiv

  let (rwWrapperRaw, numArgs) := 
    if mapLogInEquiv then 
      (`map_objFun_log, 1)
    else 
      ← rewriteWrapperLemma tagNum numConstrTags
  
  -- Different rewrite wrappers for equivalence and non-equivalence cases.
  let rwWrapper := 
    (if isEquiv then `MinimizationQ else `Minimization) ++ rwWrapperRaw

  -- Build expexcted expression to generate the right rewrite condition. Again,
  -- mapping the logarithm is an exception.
  let expectedTermStr := step.expectedTerm
  let mut expectedExpr ← EggString.toExpr vars expectedTermStr
  if !atObjFun then 
    expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
  expectedExpr ← withLocalDeclD `p domain fun p => do
    Meta.withDomainLocalDecls domain p fun xs prs => do
      let replacedFVars := Expr.replaceFVars expectedExpr fvars xs
      mkLambdaFVars #[p] (Expr.replaceFVars replacedFVars xs prs)
  if mapLogInEquiv then 
    expectedExpr ← mkFreshExprMVar none

  let (needsEq, tac) := findTactic isEquiv step.rewriteName step.direction
  let tacStx ← tac
  if needsEq then
    let toApply ← rewriteWrapperApplyExpr givenRange rwWrapper numArgs expectedExpr
    -- Goals after initial application of rewrite wrapper (the objective function or 
    -- constraint codnition has not been solved yet).
    let mut gs := []

    if !isEquiv then
      gs ← g.apply toApply
    else 
      let transGs ← evalTacticAt (← `(tactic| apply Eq.trans)) g;
      if transGs.length != 3 then 
        throwError "Equivalence mode. Expected 3 goals after applying `Eq.trans`, got {transGs.length}."
      
      let gToChange := transGs[0]!
      let nextG := transGs[1]!
      nextG.setTag `sol

      let gsAfterApply ← gToChange.apply toApply

      if gsAfterApply.length != 1 then 
        throwError "Equivalence mode. Expected 1 goal after applying rewrite wrapper, got {gsAfterApply.length}."
      
      let gToRw := gsAfterApply[0]!
      gToRw.setTag `hrw

      gs := [gToRw, nextG]

    if gs.length != 2 then 
      dbg_trace s!"Failed to rewrite {step.rewriteName} after applying the wrapper lemam."
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

    let fullTac : Syntax ← `(tactic| intros; 
      try { norm_num_clean_up; $tacStx <;> norm_num } <;>
      try { $tacStx <;> norm_num } <;>
      try { norm_num })
    let gsAfterRw ← evalTacticAt fullTac gToRw
    
    if gsAfterRw.length == 0 then
      return [gSol]
    else
      dbg_trace s!"Failed to rewrite {step.rewriteName} after rewriting constraint / objective function (equiv {isEquiv})."
      for g in gs do  
        dbg_trace s!"Could not prove {← Meta.ppGoal g}."
      return gs
  else
    -- No equality case.
    evalTacticAt tacStx g

syntax (name := convexify) "convexify" : tactic

@[tactic convexify]
def evalConvexify : Tactic := fun stx => match stx with
  | `(tactic| convexify) => withMainContext do
    normNumCleanUp (useSimp := false)

    let gTarget ← getMainTarget

    -- Generate `MinimizationExpr`, handling the equivalence case.
    let isEquiv := gTarget.isEq
    let mut gExprRaw ← liftM <| do
      if isEquiv then 
        if let some (_, lhs, _) ← matchEq? gTarget then 
          if lhs.isAppOf ``MinimizationQ.mk then 
            return lhs.getArg! 3            
          else 
            throwError "convexify expected an an Expr fo the form `MinimizationQ.mk ...`."
        else 
          throwError "convexify expected an equivalence, got {gTarget}."
      else 
        if gTarget.isAppOf ``Minimization.Solution then 
          -- Get `p` From `Solution p`.
          return gTarget.getArg! 3
        else 
          throwError "convexify expected an Expr fo the form `Solution ...`."
    
    -- Unfold if necessary.
    if let Expr.const n _ := gExprRaw then 
      unfoldTarget n
      gExprRaw := (← unfold gExprRaw n).expr

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
    let varDomainConstrs := domainConstrs.map (fun (_, v, d) => [v, d])
    let constrsToIgnore := domainConstrs.map (fun (h, _, _) => h)

    -- Remove less-than's before sending it to egg.
    let gStr := { gStr with 
      constr := gStr.constr.filter (fun (h, _) => !constrsToIgnore.contains h) }

    -- Call egg.
    let eggRequest : EggRequest := {
      domains := varDomainConstrs.data,
      target := EggMinimization.ofOCTree gStr
    }
    
    try 
      let steps ← runEggRequest eggRequest

      -- Apply steps.
      let mut g ← getMainGoal
      for step in steps do
        let gs ← evalStep g step vars fvars domain numConstrTags tagsMap isEquiv
        if gs.length != 1 then 
          dbg_trace s!"Failed to rewrite {step.rewriteName} after evaluating step ({gs.length} goals)."
        else 
          dbg_trace s!"Rewrote {step.rewriteName}."
          g := gs[0]!
        replaceMainGoal [g]

      normNumCleanUp (useSimp := false)

      saveTacticInfoForToken stx

      if isEquiv then 
        evalTactic (← `(tactic| rfl))
    catch e => 
      let eStr ← e.toMessageData.toString
      throwError "convexify failed with error: {eStr}"

  | _ => throwUnsupportedSyntax

end CvxLean
