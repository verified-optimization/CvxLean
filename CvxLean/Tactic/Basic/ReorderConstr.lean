import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Basic.ReplaceConstr

namespace CvxLean
open Lean

namespace Meta

open Std Lean.Meta

/-- -/
def reorderConstrsExpr (ids : Array Lean.Name) (e : Expr) : MetaM Expr := do
  let mut constrs : Std.HashMap Lean.Name Expr := {}
  for c in ← decomposeConstraints e do
    if constrs.contains c.1 then 
      throwError "reorder_constrs error: Constraint names are not unique: {c.1}"
    constrs := constrs.insert c.1 c.2
  let newConstrs ← ids.mapM fun id => do 
    match constrs.find? id with
    | none => throwError "reorder_constrs error: Unknown constraint: {id}"
    | some c => return c
  if constrs.size < ids.size then 
    throwError "reorder_constrs error: Too many constraints"
  if ids.size < constrs.size then 
    throwError "reorder_constrs error: Not enough constraints"
  let res := composeAnd newConstrs.data
  return res

/-- -/
def reorderConstrs (goal : MVarId) (ids : Array Lean.Name) : MetaM MVarId := do
  let goalExprs ← matchSolutionExpr goal
  let (newConstrMVar, eqGoal, newGoal) ← replaceConstr goal
  let newConstr ← 
    withLambdaBody goalExprs.constraints fun p constrBody => do
      let constrBody ← reorderConstrsExpr ids constrBody
      mkLambdaFVars #[p] constrBody
  MVarId.assign newConstrMVar newConstr

  let (_, eqGoal) ← MVarId.intro eqGoal `p
  let simpTheorems : SimpTheorems := {}
  let simpTheorems ← simpTheorems.addConst ``and_comm
  let simpTheorems ← simpTheorems.addConst ``and_left_comm
  let simpTheorems ← simpTheorems.addConst ``and_assoc
  let simpTheorems ← simpTheorems.addConst ``eq_self
  let simpRes ← simpTarget eqGoal
    {← Simp.Context.mkDefault 
      with simpTheorems := #[simpTheorems]}
  if simpRes.1.isSome then 
    throwError "reorder_constrs error: Failed to prove reordering correct: {mkMVar eqGoal}"
  return newGoal

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := reorderConstr) "reorder_constr" "[" ident,* "]" : tactic

/-- -/
@[tactic reorderConstr]
partial def evalReorderConstr : Tactic := fun stx => match stx with
| `(tactic| reorder_constr [$ids,*]) => do
  replaceMainGoal $ [← Meta.reorderConstrs (← getMainGoal) (ids.getElems.map Syntax.getId)]
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
