import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

namespace CvxLean

open Lean Meta Elab Tactic

namespace Meta

/-- -/
def replaceConstrName (name : Name) (e : Expr) : MetaM Expr := do
  let (_, e) ← decomposeLabel e
  return mkLabel name e

/-- Rename the constraints using `names`. The `names` Array can be shorter then
  the number of constraints; then only the first few constraints are renamed. -/
def renameConstrsBuilder (names : Array Lean.Name) : EquivalenceBuilder := fun eqvExpr g => do
  let lhsMinExpr ← eqvExpr.toMinimizationExprLHS

  -- Create new renamed constraints.
  let newConstrs ← withLambdaBody lhsMinExpr.constraints fun p constraints => do
    let mut constraints := (← decomposeAnd constraints).toArray
    if constraints.size < names.size then
      throwError "`rename_constrs` error: Too many constraint names. Expected {constraints.size}."
    for i in [:names.size] do
      let newConstr ← replaceConstrName names[i]! constraints[i]!
      constraints := constraints.set! i newConstr
    return ← mkLambdaFVars #[p] $ composeAnd constraints.toList
  let rhsMinExpr := { lhsMinExpr with constraints := newConstrs }

  if !(← isDefEq eqvExpr.q rhsMinExpr.toExpr) then
      throwError "`rename_constrs` error: Failed to unify the goal."

  -- Close goal by reflexivity.
  if let _ :: _ ← evalTacticAt (← `(tactic| equivalence_rfl)) g then
      throwError "`rename_constrs` error: Failed to close the goal."

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := renameConstrs) "rename_constrs" "[" ident,* "]" : tactic

/-- -/
@[tactic renameConstrs]
partial def evalRenameConstrs : Tactic := fun stx => match stx with
| `(tactic| rename_constrs [$ids,*]) => do
    let names := ids.getElems.map Syntax.getId
    (renameConstrsBuilder names).toTactic
    saveTacticInfoForToken stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
