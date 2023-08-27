import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization

namespace CvxLean

open Lean

namespace Meta

open Lean.Meta

/-- -/
def replaceConstrName (name : Lean.Name) (e : Expr) : MetaM Expr := do
  let (_, e) ← decomposeLabel e
  return mkLabel name e

/-- Rename the constraints using `names`. The `names` Array can be shorter then
  the number of constraints; then only the first few constraints are renamed. -/
def renameConstrs (goal : MVarId) (names : Array Lean.Name) : MetaM Unit := do
  let goalExprs ← SolutionExpr.fromGoal goal
  let constraints ← instantiateMVars goalExprs.constraints
  let newConstr ←
    withLambdaBody constraints fun p constraints => do
      let mut constraints := (← decomposeAnd constraints).toArray
      if @LT.lt Nat instLTNat constraints.size names.size then 
        throwError "Too many constraint names. Expected {constraints.size}."
      for i in [:names.size] do
        let newConstr ← replaceConstrName names[i]! constraints[i]!
        constraints := constraints.set! i newConstr
      return ← mkLambdaFVars #[p] $ composeAnd constraints.toList
  let goalExprs := {goalExprs with constraints := newConstr}
  MVarId.setType goal goalExprs.toExpr

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := renameConstr) "rename_constr" "[" ident,* "]" : tactic

/-- -/
@[tactic renameConstr]
partial def evalRenameConstr : Tactic := fun stx => match stx with
| `(tactic| rename_constr [$ids,*]) => do
  let ids : Array Syntax := ids
  Meta.renameConstrs (← getMainGoal) (ids.map Syntax.getId)
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
