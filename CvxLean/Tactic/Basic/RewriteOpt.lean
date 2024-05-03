import CvxLean.Meta.Minimization
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Debug
import CvxLean.Tactic.Basic.ShowVars
import CvxLean.Tactic.Basic.RenameConstrs

/-!
# Tactics for conditional rewrites

This file defines the `rw_opt`, `rw_obj`, and `rw_constr` tactics. These tactics are used to modify
a particular component, usually by rewriting it. There is also the option of using `into` to
specify the target expression exactly, e.g., `rw_constr c₁ into (0 ≤ x + y)`.

From the point of view of the user, this is similar `CvxLean/Tactic/Basic/ConvOpt.lean` in that this
tactic combinator allows us to focus on the objective function or one constraint, and apply tactics
to it. The difference is that the local context contains the constraints (other than the current one
if a constraint is being modified). This is crucial to apply rewrites that depend on conditions
established by other constraints.

For example, consider the following:
```
equivalence eqv/q :
    optimization (x : ℝ)
      minimize sqrt (x ^ 2)
      subject to
        c₁ : 0 ≤ x := by
  rw_obj =>
    -- x : ℝ, c₁ : 0 ≤ x ⊢ sqrt (x ^ 2) = ?g x
    rw [rpow_two, sqrt_sq c₁]
```
In this case, we need `c₁` to be able to rewrite `sqrt (x ^ 2) = x`. The resulting problem `q` is:
```
optimization (x : ℝ)
  minimize x
  subject to
    c₁ : 0 ≤ x
```

### TODO

* Using the lemmas of the form `rewrite_constraint_i` is ugly because we need many of them. It does
  improve performance compared to building the lemma every time. A better approach is needed here.
-/

namespace CvxLean

open Lean Meta Elab Parser Tactic

namespace Meta

/-- Find appropriate lemma to rewrite the objective function depending on the number of
constraints, which makes it easy to add them to the local context by unification. -/
def rewriteObjLemma (numConstrs : Nat) : MetaM Name :=
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
  | _  => throwRwObjError "can only rewrite problems with up to 10 constraints."

/-- This is the main equivalence builder to rewrite the objective function. It takes a tactic that
can use both the current goal and the variable representing the domain of the problem. The latter
is used in `pre_dcp` to easily build expressions. It takes care of applying the correct "congruence"
lemma to set up the local context to rewrite the objective function, and applies the tactic. -/
def rewriteObjBuilderFromTactic (shouldEval : Bool) (tac : MVarId → FVarId → TacticM Unit)
    (rhs? : Option Expr) : EquivalenceBuilder Unit :=
  fun eqvExpr g => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let constrTags ← withLambdaBody lhsMinExpr.constraints fun _ constrsBody => do
      let constrs ← decomposeConstraints constrsBody
      return constrs.map fun (n, _) => n
    let numConstrs := constrTags.length
    let gs ← g.apply (mkConst (← rewriteObjLemma numConstrs))
    let mut gToRw := g
    let mut foundGToRw := false
    for g in gs do
      let tag ← g.getTag
      if tag == `hrw then
        gToRw := g
        foundGToRw := true
      if tag == `g && rhs?.isSome then
        g.assign rhs?.get!
    if !foundGToRw then
      throwRwObjError "could not find rewrite goal."
    let (fvarIds, gAfterIntros) ← gToRw.introN (1 + numConstrs) ([`p] ++ constrTags)
    if fvarIds.size == 0 then
      throwRwObjError "could not introduce optimization variables."
    let probFVarId := fvarIds[0]!
    let gAfterShowVars ← showVars gAfterIntros (fvarIds.get! 0)
    if shouldEval then
      if let gs@(_ :: _) ← Tactic.run gAfterShowVars (tac gAfterShowVars probFVarId) then
        trace[CvxLean.debug] "`rw_obj` could not close {gs}."
        throwRwObjError "could not close all goals."

/-- Wrapper of `rewriteObjBuilderFromTactic` that takes syntax instead. -/
def rewriteObjBuilder (shouldEval : Bool) (tacStx : Syntax) (rhs? : Option Expr) :
    EquivalenceBuilder Unit :=
  fun eqvExpr g => do
    if shouldEval then
      trace[CvxLean.debug] "`rw_obj` using tactic {tacStx}."
    let tac := fun g _ => evalTacticAt tacStx g >>= setGoals
    rewriteObjBuilderFromTactic shouldEval tac rhs? eqvExpr g

/-- Same as `rewriteObjBuilder` but without a target RHS. -/
def rewriteObjBuilderWithoutTarget (shouldEval : Bool) (tacStx : Syntax) :
    EquivalenceBuilder Unit :=
  rewriteObjBuilder shouldEval tacStx none

/-- Same as `rewriteObjBuilder` but with a target RHS, given as syntax. Therefore, we need to do
some work to create an expression over the optimization variables. -/
def rewriteObjBuilderWithTarget (shouldEval : Bool) (tacStx : Syntax) (targetStx : Syntax) :
    EquivalenceBuilder Unit :=
  fun eqvExpr g => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let vars ← decomposeDomain (← instantiateMVars lhsMinExpr.domain)
    let fvars := Array.mk <| vars.map (fun ⟨n, _⟩ => mkFVar (FVarId.mk n))
    let target ← withLocalDeclD `p lhsMinExpr.domain fun p => do
      Meta.withDomainLocalDecls lhsMinExpr.domain p fun xs prs => do
        let target ← Tactic.elabTerm targetStx none
        mkLambdaFVars #[p] ((target.replaceFVars fvars xs).replaceFVars xs prs)
    rewriteObjBuilder shouldEval tacStx (some target) eqvExpr g

/-- Returns lemma to rewrite constraints at `rwIdx` and the name of the RHS parameter. Similarly to
`rewriteObjLemma`, it depends on the number of constraints to appropriately introduce the
constraints that the rewrite might depend on. -/
def rewriteConstrLemma (rwIdx : Nat) (numConstrs : Nat) : MetaM (Name × Name) :=
  if rwIdx == numConstrs then
    match rwIdx with
    | 1  => return (``Minimization.Equivalence.rewrite_constraint_1_last, `c1')
    | 2  => return (``Minimization.Equivalence.rewrite_constraint_2_last, `c2')
    | 3  => return (``Minimization.Equivalence.rewrite_constraint_3_last, `c3')
    | 4  => return (``Minimization.Equivalence.rewrite_constraint_4_last, `c4')
    | 5  => return (``Minimization.Equivalence.rewrite_constraint_5_last, `c5')
    | 6  => return (``Minimization.Equivalence.rewrite_constraint_6_last, `c6')
    | 7  => return (``Minimization.Equivalence.rewrite_constraint_7_last, `c7')
    | 8  => return (``Minimization.Equivalence.rewrite_constraint_8_last, `c8')
    | 9  => return (``Minimization.Equivalence.rewrite_constraint_9_last, `c9')
    | 10 => return (``Minimization.Equivalence.rewrite_constraint_10_last, `c10')
    | _  => throwRwConstrError "error: can only rewrite problems with up to 10 constraints."
  else
    match rwIdx with
    | 1  => return (``Minimization.Equivalence.rewrite_constraint_1, `c1')
    | 2  => return (``Minimization.Equivalence.rewrite_constraint_2, `c2')
    | 3  => return (``Minimization.Equivalence.rewrite_constraint_3, `c3')
    | 4  => return (``Minimization.Equivalence.rewrite_constraint_4, `c4')
    | 5  => return (``Minimization.Equivalence.rewrite_constraint_5, `c5')
    | 6  => return (``Minimization.Equivalence.rewrite_constraint_6, `c6')
    | 7  => return (``Minimization.Equivalence.rewrite_constraint_7, `c7')
    | 8  => return (``Minimization.Equivalence.rewrite_constraint_8, `c8')
    | 9  => return (``Minimization.Equivalence.rewrite_constraint_9, `c9')
    | 10 => return (``Minimization.Equivalence.rewrite_constraint_10, `c10')
    | _  => throwRwConstrError "can only rewrite problems with up to 10 constraints."

section RIntro

open Lean.Parser.Category

def nameToRintroPat (n : Name) : TSyntax `rcasesPat :=
  Unhygienic.run `(rcasesPat| $(Lean.mkIdent n):ident)

/-- Trick to turn a list of names into a `rintro` pattern. -/
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
  | _ => throwRwConstrError "could not apply `rintro`, too many constraints."

end RIntro

open Term

/-- This is the main equivalence builder to rewrite a constraint conditionally. It operates very
similarly to `rewriteObjBuilderFromTactic`. Some furhter work is needed here since we need to
carefully put every *other* constraint in the local context. -/
def rewriteConstrBuilderFromTactic (shouldEval : Bool) (constrTag : Name)
    (tac : MVarId → FVarId → TacticM Unit) (rhs? : Option Expr) : EquivalenceBuilder (List Name) :=
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
      throwRwConstrError "could not find constraint to rewrite."
    let (lemmaName, rhsName) ← rewriteConstrLemma rwIdx numConstrs
    let gs ← g.apply (mkConst lemmaName)
    let mut gToRw := g
    let mut foundGToRw := false
    for g in gs do
      let tag ← g.getTag
      if tag == `hrw then
        gToRw := g
        foundGToRw := true
      if tag == rhsName && rhs?.isSome then
        g.assign rhs?.get!
    if !foundGToRw then
      throwRwConstrError "could not find rewrite goal."
    -- Intros appropriately.
    let constrTagsBefore := constrTags.take rwIdx.pred
    let numConstrsBefore := constrTagsBefore.length
    let constrTagsAfter := constrTags.drop rwIdx
    let isLast := rwIdx == numConstrs
    let (probFVarId, gAfterIntros) := ← do
      let (fvarIds, gAfterIntros1) ← gToRw.introN (1 + numConstrsBefore) ([`p] ++ constrTagsBefore)
      if fvarIds.size == 0 then
        throwRwConstrError "could not introduce optimization variables."
      if isLast then
        return (fvarIds[0]!, gAfterIntros1)
      else
        let toRIntro ← namesToRintroPat constrTagsAfter
        let (gsAfterRIntro, _) ← TermElabM.run <|
          RCases.rintro #[toRIntro] none gAfterIntros1
        if gsAfterRIntro.length != 1 then
          throwRwConstrError "could not introduce optimization variables."
        return (fvarIds[0]!, gsAfterRIntro[0]!)

    let gAfterShowVars ← showVars gAfterIntros probFVarId
    if shouldEval then
      if let gs@(_ :: _) ← Tactic.run gAfterShowVars (tac gAfterShowVars probFVarId) then
        trace[CvxLean.debug] "`rw_constr` could not close {gs}."
        throwRwConstrError "could not close all goals."

    return constrTags

/-- Wrapper of `rewriteConstrBuilderFromTactic` that takes syntax instead. -/
def rewriteConstrBuilder (shouldEval : Bool) (constrTag : Name) (tacStx : Syntax)
    (rhs? : Option Expr) : EquivalenceBuilder (List Name) :=
  fun g eqvExpr => do
    if shouldEval then
      trace[CvxLean.debug] "`rw_constr` using tactic {tacStx}."
    let tac := fun g _ => evalTacticAt tacStx g >>= setGoals
    rewriteConstrBuilderFromTactic shouldEval constrTag tac rhs? g eqvExpr

/-- Same as `rewriteConstrBuilder` but without a target RHS. -/
def rewriteConstrBuilderWithoutTarget (shouldEval : Bool) (constrTag : Name) (tacStx : Syntax) :
    EquivalenceBuilder (List Name) :=
  rewriteConstrBuilder shouldEval constrTag tacStx none

/-- Same as `rewriteConstrBuilder` but with a target RHS, given as syntax. Therefore, we need to do
some work to create an expression over the optimization variables. -/
def rewriteConstrBuilderWithTarget (shouldEval : Bool) (constrTag : Name) (tacStx : Syntax)
    (targetStx : Syntax) : EquivalenceBuilder (List Name) :=
  fun eqvExpr g => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let vars ← decomposeDomain (← instantiateMVars lhsMinExpr.domain)
    let fvars := Array.mk <| vars.map (fun ⟨n, _⟩ => mkFVar (FVarId.mk n))
    let target ← withLocalDeclD `p lhsMinExpr.domain fun p => do
      Meta.withDomainLocalDecls lhsMinExpr.domain p fun xs prs => do
        let target ← Tactic.elabTerm targetStx none
        mkLambdaFVars #[p] ((target.replaceFVars fvars xs).replaceFVars xs prs)
    rewriteConstrBuilder shouldEval constrTag tacStx (some target) eqvExpr g

end Meta

namespace Tactic

/-- This tactic can be used with or without a target expression as follows: `rw_obj => ...` and
`rw_obj into rhs => ...`, where `rhs` is a term over the optimization variables. The `...` might be
replaced by any tactic block, usually rewrites. The result is an equivalent optimization problem
with the objective function modified as specified by the tactic block. The rewrites might be
conditional on the constraints. -/
syntax (name := rwObj) "rw_obj" (&" into" term)? darrow (tacticSeq)? : tactic

@[tactic rwObj]
def evalRwObjFun : Tactic := fun stx => match stx with
  | `(tactic|rw_obj =>) => do
      (rewriteObjBuilderWithoutTarget false stx).toTactic
  | `(tactic|rw_obj => $tacStx) => do
      (rewriteObjBuilderWithoutTarget true tacStx).toTactic
      saveTacticInfoForToken stx
  | `(tactic|rw_obj into $targetStx =>) => do
      (rewriteObjBuilderWithTarget false stx targetStx).toTactic
  | `(tactic|rw_obj into $targetStx => $tacStx) => do
      (rewriteObjBuilderWithTarget true tacStx targetStx).toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

/-- This tactic can be used with or without a target expression as follows: `rw_constr c₁ => ...`
and `rw_constr c₁ into rhs => ...`, where `rhs` is a term over the optimization variables. The `...`
might be replaced by any tactic block, usually rewrites. The result is an equivalent optimization
problem with the constraint `c₁` modified as specified by the tactic block. The rewrites might be
conditional on the other constraints, e.g., `c₂`, ..., `cₙ`. -/
syntax (name := rwConstr) "rw_constr " (ident)? (&" into" term)? darrow (tacticSeq)? : tactic

@[tactic rwConstr]
def evalRwConstr : Tactic := fun stx => match stx with
  | `(tactic|rw_constr $h =>) => do
      let _ ← (rewriteConstrBuilderWithoutTarget false h.getId stx).toTactic
  | `(tactic|rw_constr $h => $tacStx) => do
      let constrTags ← (rewriteConstrBuilderWithoutTarget true h.getId tacStx).toTactic
      (renameConstrsBuilder constrTags.toArray).toTactic
      saveTacticInfoForToken stx
  | `(tactic|rw_constr $h into $targetStx =>) => do
      let _ ← (rewriteConstrBuilderWithTarget false h.getId stx targetStx).toTactic
  | `(tactic|rw_constr $h into $targetStx => $tacStx) => do
      let constrTags ← (rewriteConstrBuilderWithTarget true h.getId tacStx targetStx).toTactic
      (renameConstrsBuilder constrTags.toArray).toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end Tactic
