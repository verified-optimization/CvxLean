import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

/-!
# Tactic to reorder constraints

This file defines the `reorder_constrs` tactic. It takes a list of names, e.g., `[c₂, c₁, c₃]`. This
list must be a permutation of the constraint names.

We illustrate it with an example of how to use it inside the `equivalence` command:
```
equivalence eqv/q :
    optimization (x : ℝ)
      minimize x
      subject to
        c₁ : 1 ≤ x
        c₂ : 0 < x := by
  reorder_constrs [c₂, c₁]
```
The resulting problem `q` looks as follows:
```
optimization (x : ℝ)
  minimize x
  subject to
    c₂ : 0 < x
    c₁ : 1 ≤ x
```
-/

namespace CvxLean

open Lean

namespace Meta

open Std Meta Elab Tactic

/-- Given the constraint expression `e`, look through the names and re-order them according to
`ids`. -/
def reorderConstrsExpr (ids : Array Name) (e : Expr) : MetaM Expr := do
  let mut constrs : Std.HashMap Lean.Name Expr := {}
  for (cName, cExpr) in ← decomposeConstraints e do
    if constrs.contains cName then
      throwReorderConstrsError "constraint names are not unique ({cName})."
    constrs := constrs.insert cName cExpr
  let newConstrs ← ids.mapM fun id => do
    match constrs.find? id with
    | none => throwReorderConstrsError "unknown constraint {id}."
    | some c => return c
  if constrs.size < ids.size then
    throwReorderConstrsError "too many constraints."
  if ids.size < constrs.size then
    throwReorderConstrsError "not enough constraints."
  return composeAnd newConstrs.data

/-- Use `reorderConstrsExpr` to obtain the target problem. Then, they should be equivalent by
rewriting together with `tauto`. -/
def reorderConstrsBuilder (ids : Array Name) : EquivalenceBuilder Unit := fun eqvExpr g =>
  g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let newConstrs ← withLambdaBody lhsMinExpr.constraints fun p constrBody => do
      let constrBody ← reorderConstrsExpr ids constrBody
      mkLambdaFVars #[p] constrBody
    let rhsMinExpr := { lhsMinExpr with constraints := newConstrs }

    if !(← isDefEq eqvExpr.rhs rhsMinExpr.toExpr) then
      throwReorderConstrsError "failed to unify the goal."

    if let [g] ← g.apply (mkConst ``Minimization.Equivalence.rewrite_constraints) then
      let (_, g) ← g.intros
      if let _ :: _ ← evalTacticAt (← `(tactic| tauto)) g then
        throwReorderConstrsError "failed to prove reordering correct."
    else
      throwReorderConstrsError "failed to rewrite constraints."

end Meta

namespace Tactic

open Elab Tactic Meta

/-- Tactic that takes a permutation of the current constraint names (as a list) and reusults in the
same problem with the constraints re-ordered according to the list given. -/
syntax (name := reorderConstrs) "reorder_constrs" "[" ident,* "]" : tactic

@[tactic reorderConstrs]
def evalReorderConstrs : Tactic := fun stx => match stx with
  | `(tactic| reorder_constrs [$ids,*]) => do
      let ids := ids.getElems.map Syntax.getId
      (reorderConstrsBuilder ids).toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end Tactic

end CvxLean
