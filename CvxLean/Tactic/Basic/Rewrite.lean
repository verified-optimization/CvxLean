import CvxLean.Meta.Minimization
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Basic.ShowVars

namespace CvxLean

open Lean Meta Elab Parser Tactic

namespace Meta

def rewriteObjFunLemma (numConstrs : Nat) : MetaM Name :=
  match numConstrs with
  | 1  => return ``Minimization.Equivalence.rewrite_objFun_1
  | 2  => return ``Minimization.Equivalence.rewrite_objFun_2
  | 3  => return ``Minimization.Equivalence.rewrite_objFun_3
  | 4  => return ``Minimization.Equivalence.rewrite_objFun_4
  | 5  => return ``Minimization.Equivalence.rewrite_objFun_5
  | 6  => return ``Minimization.Equivalence.rewrite_objFun_6
  | 7  => return ``Minimization.Equivalence.rewrite_objFun_7
  | 8  => return ``Minimization.Equivalence.rewrite_objFun_8
  | 9  => return ``Minimization.Equivalence.rewrite_objFun_9
  | 10 => return ``Minimization.Equivalence.rewrite_objFun_10
  | _  => throwError "`rw_objFun` error: can only rewrite problems with up to 10 constraints."

/-- -/
def rewriteObjFunBuilder (tacStx : Syntax) : EquivalenceBuilder :=
  fun eqvExpr g => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let constrTags ← withLambdaBody lhsMinExpr.constraints fun _ constrsBody => do
      let constrs ← decomposeConstraints constrsBody
      return constrs.map fun (n, _) => n
    let numConstrs := constrTags.length
    let gs ← g.apply (mkConst (← rewriteObjFunLemma numConstrs))
    let mut gToRw := g
    let mut foundGToRw := false
    for g in gs do
      if (← g.getTag) == `hrw then
        gToRw := g
        foundGToRw := true
    if !foundGToRw then
      throwError "`rw_objFun` error: could not find rewrite goal."
    let (fvarIds, gAfterIntros) ← gToRw.introN (1 + numConstrs) ([`p] ++ constrTags)
    if fvarIds.size == 0 then
      throwError "`rw_objFun` error: could not introduce optimization variables."
    let gAfterShowVars ← showVars gAfterIntros (fvarIds.get! 0)
    if let _ :: _ ← evalTacticAt tacStx gAfterShowVars then
      throwError "`rw_objFun` error: could not close all goals."

/-- -/
def rewriteConstrLemma (rwIdx : Nat) (numConstrs : Nat) : MetaM Name :=
  if rwIdx == numConstrs then
    match rwIdx with
    | 1  => return ``Minimization.Equivalence.rewrite_constraint_1_last
    | 2  => return ``Minimization.Equivalence.rewrite_constraint_2_last
    | 3  => return ``Minimization.Equivalence.rewrite_constraint_3_last
    | 4  => return ``Minimization.Equivalence.rewrite_constraint_4_last
    | 5  => return ``Minimization.Equivalence.rewrite_constraint_5_last
    | 6  => return ``Minimization.Equivalence.rewrite_constraint_6_last
    | 7  => return ``Minimization.Equivalence.rewrite_constraint_7_last
    | 8  => return ``Minimization.Equivalence.rewrite_constraint_8_last
    | 9  => return ``Minimization.Equivalence.rewrite_constraint_9_last
    | 10 => return ``Minimization.Equivalence.rewrite_constraint_10_last
    | _  => throwError "`rw_constr` error: can only rewrite problems with up to 10 constraints."
  else
    match rwIdx with
    | 1  => return ``Minimization.Equivalence.rewrite_constraint_1
    | 2  => return ``Minimization.Equivalence.rewrite_constraint_2
    | 3  => return ``Minimization.Equivalence.rewrite_constraint_3
    | 4  => return ``Minimization.Equivalence.rewrite_constraint_4
    | 5  => return ``Minimization.Equivalence.rewrite_constraint_5
    | 6  => return ``Minimization.Equivalence.rewrite_constraint_6
    | 7  => return ``Minimization.Equivalence.rewrite_constraint_7
    | 8  => return ``Minimization.Equivalence.rewrite_constraint_8
    | 9  => return ``Minimization.Equivalence.rewrite_constraint_9
    | 10 => return ``Minimization.Equivalence.rewrite_constraint_10
    | _  => throwError "`rw_constr` error: can only rewrite problems with up to 10 constraints."

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
