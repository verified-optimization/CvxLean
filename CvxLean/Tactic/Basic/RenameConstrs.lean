import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

/-!
# Tactic to rename constraints

This file defines the `rename_constrs` tactic. It takes a list of names, e.g., `[c₁, c₂, c₃]`. The
list must have the same length as the number of constraints in the current problem.

We illustrate it with an example of how to use it inside the `equivalence` command:
```
equivalence eqv/q :
    optimization (x : ℝ)
      minimize x
      subject to
        c₁ : 1 ≤ x
        c₂ : 0 < x := by
  rename_constrs [h₁, h₂]
```
The resulting problem `q` looks as follows:
```
optimization (x : ℝ)
  minimize x
  subject to
    h₁ : 1 ≤ x
    h₂ : 0 < x
```
-/

namespace CvxLean

open Lean Meta Elab Tactic

namespace Meta

/-- Split meta-data into (CvxLean) label and expression and replace the label with `name`. -/
def replaceConstrName (name : Name) (e : Expr) : MetaM Expr := do
  let (_, e) ← decomposeLabel e
  return mkLabel name e

/-- Rename the constraints using `names`. The `names` Array can be shorter then
  the number of constraints; then only the first few constraints are renamed. -/
def renameConstrsBuilder (names : Array Name) : EquivalenceBuilder Unit := fun eqvExpr g => do
  let lhsMinExpr ← eqvExpr.toMinimizationExprLHS

  -- Create new renamed constraints.
  let newConstrs ← withLambdaBody lhsMinExpr.constraints fun p constraints => do
    let mut constraints := (← decomposeAnd constraints).toArray
    if constraints.size < names.size then
      throwRenameConstrsError "too many constraint names. Expected {constraints.size}."
    for i in [:names.size] do
      let newConstr ← replaceConstrName names[i]! constraints[i]!
      constraints := constraints.set! i newConstr
    return ← mkLambdaFVars #[p] <| composeAnd constraints.toList
  let rhsMinExpr := { lhsMinExpr with constraints := newConstrs }

  if !(← isDefEq eqvExpr.rhs rhsMinExpr.toExpr) then
      throwRenameConstrsError "failed to unify the goal."

  -- Close goal by reflexivity.
  if let _ :: _ ← evalTacticAt (← `(tactic| equivalence_rfl)) g then
      throwRenameConstrsError "failed to close the goal."

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

/-- Tactic to rename all constraints given a list of names. This does not change the mathematical
interpretation of the problem. -/
syntax (name := renameConstrs) "rename_constrs" "[" ident,* "]" : tactic

@[tactic renameConstrs]
partial def evalRenameConstrs : Tactic := fun stx => match stx with
| `(tactic| rename_constrs [$ids,*]) => do
    let names := ids.getElems.map Syntax.getId
    (renameConstrsBuilder names).toTactic
    saveTacticInfoForToken stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
