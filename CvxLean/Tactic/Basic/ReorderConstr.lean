import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Basic.ReplaceConstr
import CvxLean.Lib.Missing.Mathlib

attribute [-instance] coeDecidableEq

namespace CvxLean
open Lean

namespace Meta

open Std Lean.Meta

/-- -/
def reorderConstrsExpr (ids : Array Lean.Name) (e : Expr) : MetaM Expr := do
  let mut constrs : HashMap Lean.Name Expr := {}
  for c in ← decomposeConstraints e do
    if constrs.contains c.1 then throwError "Constraint names are not unique: {c.1}"
    constrs := constrs.insert c.1 c.2
  let newConstrs ← ids.mapM fun id => do 
    match constrs.find? id with
    | none => throwError "Unknown constraint: {id}"
    | some c => return c
  -- TODO: use <.
  if @LT.lt ℕ instLTNat constrs.size ids.size then throwError "Too many Constraints"
  if @LT.lt ℕ instLTNat ids.size constrs.size then throwError "Not enough Constraints"
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
  if simpRes.isSome then throwError "Failed to prove reordering correct: {mkMVar eqGoal}"
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
