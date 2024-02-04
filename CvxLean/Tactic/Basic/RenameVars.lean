import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Expr

namespace CvxLean

open Lean Expr Meta Elab Tactic

namespace Meta

/-- -/
def renameVarsBuilder (names : Array Lean.Name) : EquivalenceBuilder := fun eqvExpr g => do
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

syntax (name := renameVars) "rename_vars" "[" ident,* "]" : tactic

/-- -/
@[tactic renameVars]
partial def evalRenameVars : Tactic := fun stx => match stx with
| `(tactic| rename_vars [$ids,*]) => do
    let names := (ids.elemsAndSeps.map Syntax.getId).filter (· != Lean.Name.anonymous)
    (renameVarsBuilder names).toTactic
    saveTacticInfoForToken stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
