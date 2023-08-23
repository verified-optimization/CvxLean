import Lean
import Mathlib.Tactic.NormNum
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
def findTactic : String → EggRewriteDirection → Bool × MetaM (TSyntax `tactic)
  -- NOTE(RFM): Only instance of a rewriting without proving equality. It is 
  -- also the only case where only one direction is allowed.
  | "map_objFun_log", EggRewriteDirection.Forward =>
    (false, `(tactic| map_objFun_log))
  | rewriteName, direction => (true, do
    match ← getTacticFromRewriteName rewriteName with 
    | some tac => return tac
    | _ => throwError "Unknown rewrite name {rewriteName}({direction}).")

/-- Given the rewrite index (`0` for objective function, `1` to `numConstr` for 
for for constraints), return the rewrite lemma that needs to be applied. Also 
return the number of arguments of each rewrite lemma to be able to build an 
expression in `rewriteWrapperApplyExpr`. -/
def rewriteWrapperLemma (rwIdx : Nat) (numConstrs : Nat) : MetaM (Name × Nat) := 
  if rwIdx == 0 then 
    return (`Minimization.rewrite_objective, 1)
  else if numConstrs == 1 then 
    -- Rewriting a single constraint is the same as rewriting all constraints.
    return (`Minimization.rewrite_constraints, 1)
  else if rwIdx == numConstrs then 
    match rwIdx with 
    | 1  => return (`Minimization.rewrite_constraint_1_last,  1)
    | 2  => return (`Minimization.rewrite_constraint_2_last,  2)
    | 3  => return (`Minimization.rewrite_constraint_3_last,  3)
    | 4  => return (`Minimization.rewrite_constraint_4_last,  4)
    | 5  => return (`Minimization.rewrite_constraint_5_last,  5)
    | 6  => return (`Minimization.rewrite_constraint_6_last,  6)
    | 7  => return (`Minimization.rewrite_constraint_7_last,  7)
    | 8  => return (`Minimization.rewrite_constraint_8_last,  8)
    | 9  => return (`Minimization.rewrite_constraint_9_last,  9)
    | 10 => return (`Minimization.rewrite_constraint_10_last, 10)
    | _  => throwError "convexify can only rewrite problems with up to 10 constraints."
  else
    match rwIdx with 
    | 1  => return (`Minimization.rewrite_constraint_1,  1)
    | 2  => return (`Minimization.rewrite_constraint_2,  2)
    | 3  => return (`Minimization.rewrite_constraint_3,  3)
    | 4  => return (`Minimization.rewrite_constraint_4,  4)
    | 5  => return (`Minimization.rewrite_constraint_5,  5)
    | 6  => return (`Minimization.rewrite_constraint_6,  6)
    | 7  => return (`Minimization.rewrite_constraint_7,  7)
    | 8  => return (`Minimization.rewrite_constraint_8,  8)
    | 9  => return (`Minimization.rewrite_constraint_9,  9)
    | 10 => return (`Minimization.rewrite_constraint_10, 10)
    | _  => throwError "convexify can only rewrite problems with up to 10 constraints."

/-- -/
def rewriteWrapperApplyExpr (rwName : Name) (numArgs : Nat) (expected : Expr) : 
  MetaM Expr := do
  let signature := #[← mkFreshExprMVar none, Lean.mkConst `Real, ← mkFreshExprMVar none]
  let args ← Array.range numArgs |>.mapM fun _ => mkFreshExprMVar none
  return mkAppN (mkConst rwName) (signature ++ args ++ #[expected])

/-- Version of `norm_num` used to get rid of the `OfScientific`s. -/
def norm_num_clean_up (useSimp : Bool) : TacticM Unit :=
  Mathlib.Meta.NormNum.elabNormNum mkNullNode mkNullNode (useSimp := useSimp)

elab "convexify" : tactic => withMainContext do
  norm_num_clean_up (useSimp := false)

  let g ← getMainGoal
  
  -- NOTE(RFM): No whnf.              
  let gTy := (← MVarId.getDecl g).type
  let gExpr ← Meta.matchSolutionExprFromExpr gTy

  -- Get optimization variables.
  let vars ← withLambdaBody gExpr.constraints fun p _ => do
    let pr ← Meta.mkProjections gExpr.domain p
    return pr.map (Prod.fst)
  let varsStr := vars.map toString
  let fvars := Array.mk $ vars.map (fun v => mkFVar (FVarId.mk v))
  let domain := Meta.composeDomain <| vars.map (fun v => (v, Lean.mkConst ``Real))

  -- Get goal as tree and tags.
  let (gStr, nonnegVars) ← ExtendedEggTree.fromMinimization gExpr varsStr
  let numConstrTags := gStr.constr.size
  let mut tagsMap := HashMap.empty
  tagsMap := tagsMap.insert "objFun" 0 
  let mut idx := 1
  for (h, _) in gStr.constr do
    tagsMap := tagsMap.insert h idx 
    idx := idx + 1

  -- Call egg.
  let eggRequest := {
    domains := Array.data <| nonnegVars.map (fun v => [v, "NonNeg"]),
    target := EggMinimization.ofOCTree gStr
  }
  let steps ← runEggRequest eggRequest

  for step in steps do
    let g ← getMainGoal

    let tag := step.location
    let tagNum := tagsMap.find! tag
    let (rwWrapper, numIntros) ← rewriteWrapperLemma tagNum numConstrTags
    dbg_trace s!"Rewriting {step.rewriteName} at {tag} ({tagNum}). {rwWrapper}."

    let expectedTermStr := step.expectedTerm
    let mut expectedExpr ← EggString.toExpr vars expectedTermStr
    if tagNum > 0 then 
      expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
    expectedExpr ← withLocalDeclD `p domain fun p => do
      Meta.withDomainLocalDecls domain p fun xs prs => do
        let replacedFVars := Expr.replaceFVars expectedExpr fvars xs
        mkLambdaFVars #[p] $ Expr.replaceFVars replacedFVars xs prs

    let (needsEq, tac) := findTactic step.rewriteName step.direction
    let tacStx ← tac
    if needsEq then
      let gs ← g.apply <| ← rewriteWrapperApplyExpr rwWrapper numIntros expectedExpr

      if gs.length != 2 then 
        dbg_trace s!"Failed to rewrite {step.rewriteName}."
        replaceMainGoal gs; break

      let gToRw := gs[0]!
      let gToRwTag ← gToRw.getTag

      if gToRwTag != `hrw then 
        dbg_trace s!"Unexpected tag name {gToRwTag} when rewriting {step.rewriteName}."
        replaceMainGoal gs; break
      
      let gSol := gs[1]!
      let gSolTag ← gSol.getTag

      if gSolTag != `sol then
        dbg_trace s!"Unexpected tag name {gSolTag} when rewriting {step.rewriteName}."
        replaceMainGoal gs; break

      gSol.setTag Name.anonymous

      dbg_trace s!"To rewrite {← Meta.ppGoal gToRw}."

      let fullTac : Syntax ← `(tactic| intros; $tacStx <;> norm_num)
      let gsAfterRw ← evalTacticAt fullTac gToRw

      if gsAfterRw.length == 0 then
        dbg_trace s!"Rewrote {step.rewriteName}."
        replaceMainGoal [gSol]
      else
        dbg_trace s!"Failed to rewrite {step.rewriteName}."
        replaceMainGoal (gs ++ gsAfterRw); break
    else
      let gs ← evalTacticAt tacStx g
      dbg_trace s!"Rewrote {step.rewriteName}."
      replaceMainGoal gs

  norm_num_clean_up (useSimp := false)

  return ()

end CvxLean
