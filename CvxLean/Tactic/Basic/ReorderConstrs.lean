import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

namespace CvxLean

open Lean

namespace Meta

open Std Meta Elab Tactic

/-- -/
def reorderConstrsExpr (ids : Array Name) (e : Expr) : MetaM Expr := do
  let mut constrs : Std.HashMap Lean.Name Expr := {}
  for (cName, cExpr) in ← decomposeConstraints e do
    if constrs.contains cName then
      throwError "`reorder_constrs` error: Constraint names are not unique: {cName}."
    constrs := constrs.insert cName cExpr
  let newConstrs ← ids.mapM fun id => do
    match constrs.find? id with
    | none => throwError "`reorder_constrs` error: Unknown constraint: {id}"
    | some c => return c
  if constrs.size < ids.size then
    throwError "`reorder_constrs` error: Too many constraints"
  if ids.size < constrs.size then
    throwError "`reorder_constrs` error: Not enough constraints"
  return composeAnd newConstrs.data

/-- -/
def reorderConstrsBuilder (ids : Array Name) : EquivalenceBuilder := fun eqvExpr g =>
  g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let newConstrs ← withLambdaBody lhsMinExpr.constraints fun p constrBody => do
      let constrBody ← reorderConstrsExpr ids constrBody
      mkLambdaFVars #[p] constrBody
    let rhsMinExpr := { lhsMinExpr with constraints := newConstrs }

    if !(← isDefEq eqvExpr.q rhsMinExpr.toExpr) then
      throwError "`reorder_constrs` error: Failed to unify the goal."

    if let [g] ← g.apply (mkConst ``Minimization.Equivalence.rewrite_constraints) then
      let (_, g) ← g.intros
      if let _ :: _ ← evalTacticAt (← `(tactic| tauto)) g then
        throwError "`reorder_constrs` error: Failed to prove reordering correct."
    else
      throwError "`reorder_constrs` error: Failed to rewrite constraints."

end Meta

namespace Tactic

open Elab Tactic Meta

syntax (name := reorderConstrs) "reorder_constrs" "[" ident,* "]" : tactic

/-- -/
@[tactic reorderConstrs]
def evalReorderConstrs : Tactic := fun stx => match stx with
  | `(tactic| reorder_constrs [$ids,*]) => do
      let ids := ids.getElems.map Syntax.getId
      (reorderConstrsBuilder ids).toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end Tactic

end CvxLean
