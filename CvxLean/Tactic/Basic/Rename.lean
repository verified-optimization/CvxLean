import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Basic.DomainEquiv
import CvxLean.Lib.Missing.Mathlib

attribute [-instance] coeDecidableEq

namespace CvxLean

open Lean

namespace Meta

open Lean.Meta

/-- -/
partial def renameOptVar (goal : MVarId) (names : Array Lean.Name) : MetaM MVarId := do
  let goalExprs ← matchSolutionExpr goal
  let vars ← decomposeDomain (← instantiateMVars goalExprs.domain')
  let vars ← manipulateVars vars names.data
  let newDomain := composeDomain vars
  let newGoal ← match ← domainEquiv goal (mkApp (mkConst ``Equiv.refl [levelOne]) newDomain) with
    | [newGoal] => pure newGoal
    | _ => throwError "Unexpected number of subgoals"
  return newGoal
where manipulateVars : List (Lean.Name × Expr) → List Lean.Name → MetaM (List (Lean.Name × Expr))
| List.cons (n, ty) vars, List.cons newName newNames => return (newName, ty) :: (← manipulateVars vars newNames)
| [],                     List.cons newName newNames => throwError "Too many variable names given"
| vars,                   []                  => return vars

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := renameOptVar) "rename_opt_var" "[" ident,* "]" : tactic

/-- -/
@[tactic renameOptVar]
partial def evalRenameOptVar : Tactic := fun stx => match stx with
| `(tactic| rename_opt_var [$ids,*]) => do
  let goal ← getMainGoal
  let names := Array.map Syntax.getId ids
  replaceMainGoal [← Meta.renameOptVar goal names]
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
