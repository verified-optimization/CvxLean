import CvxLean.Meta.Minimization
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Error

/-!
# Clean up compositions

Simple equivalence-preserving tactic that removes occurrences of `∘` (`Function.comp`) from the
objective function and constraints. These may appear after a map is applied to the problem.
-/

namespace CvxLean

open Lean Meta Elab Tactic

namespace Meta

/-- Pre-process objective functions and constraints that have resulted from composing a function. -/
def cleanUpCompAux (e : Expr) (name : String) : MetaM Expr := do
  match e with
  | .app (.app (.app (.app (.app (.const ``Function.comp lvls) ty₁) ty₂) ty₃) f₁) f₂ => do
      let f₂ ← instantiateMVars <| ← whnf f₂
      let f₁ ← instantiateMVars f₁
      return mkApp5 (mkConst ``Function.comp lvls) ty₁ ty₂ ty₃ f₁ f₂
  | _ => throwError "{name} not of the form '... ∘ ...'"

/-- Trivially builds an equivalence by simplifying `Function.comp` on the problem, essentially,
pushing all function compositions. -/
def cleanUpCompBuilder : EquivalenceBuilder Unit := fun eqvExpr g => g.withContext do
  let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
  let newObjFun ← cleanUpCompAux lhsMinExpr.objFun "objFun"
  let newConstraints ← cleanUpCompAux lhsMinExpr.constraints "constr"
  let rhsMinExpr := { lhsMinExpr with objFun := newObjFun, constraints := newConstraints }
  let newEqvExpr := { eqvExpr with lhs := lhsMinExpr.toExpr, rhs := rhsMinExpr.toExpr }
  if (← isDefEq (mkMVar g) newEqvExpr.toExpr) then
    throwError "`clean_up_comp` error: Failed to unify the goal."
  let simpComp ← ({} : SimpTheorems).addDeclToUnfold ``Function.comp
  let simpContext := { config := {}, simpTheorems := #[simpComp] }
  if let (some newGoal, _) ← simpTarget g simpContext then
    if let _ :: _ ← evalTacticAt (← `(tactic| equivalence_rfl)) newGoal then
      throwError "`clean_up_comp` error: Failed to close the goal."

end Meta

namespace Tactic

open Elab Tactic

/-- Tactic that removes `∘` from the optimization problem by applying function compositions (see
`Function.comp_apply`). -/
syntax (name := cleanUpComp) "clean_up_comp" : tactic

@[tactic cleanUpComp]
def evalCleanUpComp : Tactic := fun stx => match stx with
  | `(tactic| clean_up_comp) => do
      cleanUpCompBuilder.toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end Tactic
