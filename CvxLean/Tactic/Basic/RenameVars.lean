import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

namespace CvxLean

open Lean Meta Elab Tactic

namespace Meta

/-- -/
partial def renameVarsBuilder (names : Array Lean.Name) : EquivalenceBuilder :=
  fun eqvExpr g _ => do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let vars ← decomposeDomain (← instantiateMVars eqvExpr.domainP)
    let fvars := Array.mk <| vars.map (fun ⟨n, _⟩ => mkFVar (FVarId.mk n))

    -- Create new domain.
    let renamedVars ← manipulateVars vars names.data
    let newDomain := composeDomain renamedVars
    let newFVars := Array.mk <| renamedVars.map (fun ⟨n, _⟩ => mkFVar (FVarId.mk n))

    -- Create new minimization expression.
    let newObjFun ← withLambdaBody lhsMinExpr.objFun fun p objFunBody => do
        let newObjFunBody := objFunBody.replaceFVars fvars newFVars
        mkLambdaFVars #[p] newObjFunBody
    let newConstrs ← withLambdaBody lhsMinExpr.constraints fun p constrsBody => do
        let newConstrsBody := constrsBody.replaceFVars fvars newFVars
        mkLambdaFVars #[p] newConstrsBody
    let rhsMinExpr : MinimizationExpr :=
      { domain := newDomain,
        codomain := lhsMinExpr.codomain,
        objFun := newObjFun,
        constraints := newConstrs }
    if !(← isDefEq eqvExpr.q rhsMinExpr.toExpr) then
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
    (renameVarsBuilder names).toTactic stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
