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
def rewriteObjFunBuilder (shouldEval : Bool) (tacStx : Syntax) : EquivalenceBuilder :=
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
    if shouldEval then
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

section RIntro

open Lean.Parser.Category Std.Tactic.RCases

def nameToRintroPat (n : Name) : TSyntax `rcasesPat :=
  Unhygienic.run `(rcasesPat| $(Lean.mkIdent n):ident)

def namesToRintroPat (names : List Name) : MetaM (TSyntax `rcasesPat) := do
  let ns := names.map nameToRintroPat
  match ns with
  | [n] => return n
  | [n1, n2] => return ← `(rcasesPat| ⟨$n1, $n2⟩)
  | [n1, n2, n3] => return ← `(rcasesPat| ⟨$n1, $n2, $n3⟩)
  | [n1, n2, n3, n4] => return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4⟩)
  | [n1, n2, n3, n4, n5] => return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4, $n5⟩)
  | [n1, n2, n3, n4, n5, n6] => return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4, $n5, $n6⟩)
  | [n1, n2, n3, n4, n5, n6, n7] => return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4, $n5, $n6, $n7⟩)
  | [n1, n2, n3, n4, n5, n6, n7, n8] =>
      return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4, $n5, $n6, $n7, $n8⟩)
  | [n1, n2, n3, n4, n5, n6, n7, n8, n9] =>
      return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4, $n5, $n6, $n7, $n8, $n9⟩)
  | [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10] =>
      return ← `(rcasesPat| ⟨$n1, $n2, $n3, $n4, $n5, $n6, $n7, $n8, $n9, $n10⟩)
  | _ => throwError "`rw_constr` error: could not apply `rintro`, too many constraints."

end RIntro

open Term

#check TermElabM.run

/-- -/
def rewriteConstrBuilder (shouldEval : Bool) (constrTag : Name) (tacStx : Syntax) :
    EquivalenceBuilder :=
  fun eqvExpr g => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let constrTags ← withLambdaBody lhsMinExpr.constraints fun _ constrsBody => do
      let constrs ← decomposeConstraints constrsBody
      return constrs.map fun (n, _) => n
    let numConstrs := constrTags.length
    let mut rwIdx := 0
    for i in [0:numConstrs] do
      if constrTags[i]! == constrTag then
        rwIdx := i + 1
    if rwIdx == 0 then
      throwError "`rw_constr` error: could not find constraint to rewrite."
    let gs ← g.apply (mkConst (← rewriteConstrLemma rwIdx numConstrs))
    let mut gToRw := g
    let mut foundGToRw := false
    for g in gs do
      if (← g.getTag) == `hrw then
        gToRw := g
        foundGToRw := true
    if !foundGToRw then
      throwError "`rw_constr` error: could not find rewrite goal."
    -- Intros appropriately.
    let constrTagsBefore := constrTags.take rwIdx.pred
    let numConstrsBefore := constrTagsBefore.length
    let constrTagsAfter := constrTags.drop rwIdx
    let isLast := rwIdx == numConstrs
    let (probFVarId, gAfterIntros) := ← do
      let (fvarIds, gAfterIntros1) ← gToRw.introN (1 + numConstrsBefore) ([`p] ++ constrTagsBefore)
      if fvarIds.size == 0 then
        throwError "`rw_constr` error: could not introduce optimization variables."
      if isLast then
        return (fvarIds[0]!, gAfterIntros1)
      else
        let toRIntro ← namesToRintroPat constrTagsAfter
        trace[Meta.debug] "toRIntro: {toRIntro} {constrTagsAfter} {constrTagsBefore}"
        let (gsAfterRIntro, _) ← TermElabM.run <|
          Std.Tactic.RCases.rintro #[toRIntro] none gAfterIntros1
        trace[Meta.debug] "gsAfterRIntro: {gsAfterRIntro}"
        if gsAfterRIntro.length != 1 then
          throwError "`rw_constr` error: could not introduce optimization variables."
        return (fvarIds[0]!, gsAfterRIntro[0]!)

    let gAfterShowVars ← showVars gAfterIntros probFVarId
    if shouldEval then
      if let _ :: _ ← evalTacticAt tacStx gAfterShowVars then
        throwError "`rw_constr` error: could not close all goals."

end Meta

namespace Tactic

syntax (name := rwObjFun) "rw_objFun" "=>" (tacticSeqIndentGt)? : tactic

@[tactic rwObjFun]
def evalRwObjFun : Tactic := fun stx => match stx with
  | `(tactic|rw_objFun => $tacStx) => do
      (rewriteObjFunBuilder true tacStx).toTactic
  | `(tactic|rw_objFun =>) => do
      (rewriteObjFunBuilder false stx).toTactic
  | _ => throwUnsupportedSyntax

syntax (name := rwConstr) "rw_constr" (ident)? "=>" (tacticSeq)? : tactic

@[tactic rwConstr]
def evalRwConstr : Tactic := fun stx => match stx with
  | `(tactic|rw_constr $h => $tacStx) => do
      (rewriteConstrBuilder true h.getId tacStx).toTactic
  | `(tactic|rw_constr $h =>) => do
      (rewriteConstrBuilder false h.getId stx).toTactic
  | _ => throwUnsupportedSyntax

end Tactic
