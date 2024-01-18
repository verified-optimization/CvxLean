import CvxLean.Meta.Minimization
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Basic.ShowVars

namespace CvxLean

open Lean Meta Elab Parser Tactic

namespace Meta

/-- -/
def rewriteObjFunBuilder (tacStx : Syntax) : EquivalenceBuilder :=
  fun eqvExpr g => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let constrTags ← withLambdaBody lhsMinExpr.constraints fun p constrsBody => do
      let constrs ← decomposeConstraints constrsBody
      return constrs.map fun (n, _) => n
    let gs ← g.apply (mkConst ``Minimization.Equivalence.rewrite_objFun)
    let mut gToRw := g
    let mut foundGToRw := false
    for g in gs do
      if (← g.getTag) == `hrw then
        gToRw := g
        foundGToRw := true
    if !foundGToRw then
      throwError "`rw_objFun` error: could not find rewrite goal."
    let (fvarIds, gAfterIntros) ← gToRw.introN (1 + constrTags.length) ([`p] ++ constrTags)
    if fvarIds.size == 0 then
      throwError "`rw_objFun` error: could not introduce optimization variables."
    let gAfterShowVars ← showVars gAfterIntros (fvarIds.get! 0)
    if let _ :: _ ← evalTacticAt tacStx gAfterShowVars then
      throwError "`rw_objFun` error: could not close all goals."

/-- -/
def rewriteConstrBuilder : EquivalenceBuilder := fun eqvExpr g => g.withContext do
  sorry

end Meta

namespace Tactic

syntax (name := rwObjFun) "rw_objFun" "=>" (tacticSeqIndentGt)? : tactic

syntax (name := rwConstr) "rw_constr" (ident)? "=>" (tacticSeq)? : tactic

@[tactic rwObjFun]
def evalRwObjFun : Tactic := fun stx => match stx with
  | `(tactic|rw_objFun => $tacStx) => do
      (rewriteObjFunBuilder tacStx).toTactic
  | _ => throwUnsupportedSyntax

end Tactic
