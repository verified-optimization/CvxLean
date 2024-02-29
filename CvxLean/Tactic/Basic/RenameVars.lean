import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Expr

/-!
# Tactic to rename variables

This file defines the `rename_vars` tactic. It takes a list of names, e.g., `[x, y, z]`. The
list must have the same length as the number of optimization variables in the current problem.

We illustrate it with an example of how to use it inside the `equivalence` command:
```
equivalence eqv/q :
    optimization (x y z : ℝ)
      minimize x + y + z
      subject to
        c₁ : 1 ≤ x
        c₂ : 1 ≤ y
        c₃ : 1 ≤ z := by
  rename_constrs [a, b, c]
```
The resulting problem `q` looks as follows:
```
optimization (a b c : ℝ)
  minimize a + b + c
  subject to
    c₁ : 1 ≤ a
    c₂ : 1 ≤ b
    c₃ : 1 ≤ c
```
-/

namespace CvxLean

open Lean Expr Meta Elab Tactic

namespace Meta

/-- Get the domain type, and replace the variables names stored in it (as meta-data) by the new
variable names. The resulting problem is the same expression with the new domain type. -/
def renameVarsBuilder (names : Array Name) : EquivalenceBuilder Unit := fun eqvExpr g => do
  let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
  let vars ← decomposeDomain (← instantiateMVars eqvExpr.domainLHS)

  -- Create new domain.
  let renamedVars ← manipulateVars vars names.data
  let newDomain := composeDomain renamedVars

  -- Create new minimization expression.
  let newObjFun ← withLocalDeclD `p newDomain fun p => do
    let objFunBody := mkAppNBeta lhsMinExpr.objFun #[p]
    mkLambdaFVars #[p] objFunBody
  let newConstrs ← withLocalDeclD `p newDomain fun p => do
    let objFunBody := mkAppNBeta lhsMinExpr.constraints #[p]
    mkLambdaFVars #[p] objFunBody
  let rhsMinExpr : MinimizationExpr :=
    { domain := newDomain,
      codomain := lhsMinExpr.codomain,
      objFun := newObjFun,
      constraints := newConstrs }
  if !(← isDefEq eqvExpr.rhs rhsMinExpr.toExpr) then
    throwError "`rename_vars` error: Failed to unify the goal."

  -- Close goal by reflexivity.
  if let _ :: _ ← evalTacticAt (← `(tactic| equivalence_rfl)) g then
    throwError "`rename_vars` error: Failed to close the goal."
where
  manipulateVars : List (Name × Expr) → List Name → MetaM (List (Name × Expr))
    | (_, ty) :: vars, newName :: newNames =>
        return (newName, ty) :: (← manipulateVars vars newNames)
    | [], _ :: _ => throwError "Too many variable names given"
    | vars, [] => return vars

end Meta

namespace Tactic

/-- Tactic to rename all optimization variables given a list of names. This does not change the
mathematical interpretation of the problem. -/
syntax (name := renameVars) "rename_vars" "[" ident,* "]" : tactic

@[tactic renameVars]
partial def evalRenameVars : Tactic := fun stx => match stx with
| `(tactic| rename_vars [$ids,*]) => do
    let names := (ids.elemsAndSeps.map Syntax.getId).filter (· != Lean.Name.anonymous)
    (renameVarsBuilder names).toTactic
    saveTacticInfoForToken stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
