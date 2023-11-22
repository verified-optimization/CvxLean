import CvxLean.Meta.Minimization

namespace CvxLean

open Lean

namespace Meta

open Lean.Meta

/-- -/
def cleanUpCompAux (e : Expr) (name : String) : MetaM Expr := do
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app
      (Expr.const `Function.comp lvls) ty₁) ty₂) ty₃) f₁) f₂ => do
    let f₂ ← instantiateMVars $ ← whnf f₂
    let f₁ ← instantiateMVars f₁
    return mkApp5 (mkConst `Function.comp lvls) ty₁ ty₂ ty₃ f₁ f₂
  | _ => throwError "{name} not of the form '... ∘ ...'"

/-- -/
def cleanUpComp (goal : MVarId) : MetaM MVarId := do
  let goalExprs ← SolutionExpr.fromGoal goal
  let newObjFun ← cleanUpCompAux goalExprs.objFun "objFun"
  let newConstraints ← cleanUpCompAux goalExprs.constraints "constr"
  let newGoalType := {goalExprs with objFun := newObjFun, constraints := newConstraints}.toExpr
  MVarId.setType goal newGoalType
  let simpTheorems ← ({} : SimpTheorems).addDeclToUnfold ``Function.comp
  let simpContext := { config := {}, simpTheorems := #[simpTheorems] }
  if let (some newGoal, _) ← simpTarget goal simpContext then 
    return newGoal
  else throwError "unexpected number of subgoals"

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic

syntax (name := cleanUpComp) "clean_up_comp" : tactic

/-- -/
@[tactic cleanUpComp]
partial def evalCleanUpComp : Tactic
| `(tactic| clean_up_comp) => do
  let goal ← Elab.Tactic.getMainGoal
  replaceMainGoal $ [← Meta.cleanUpComp goal]
| _ => throwUnsupportedSyntax

end Tactic