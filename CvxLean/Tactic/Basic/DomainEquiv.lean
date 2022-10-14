import Lean
import CvxLean.Lib.Minimization
import CvxLean.Tactic.Basic.CleanUpComp

attribute [-instance] coeDecidableEq

namespace CvxLean

open Lean

namespace Meta

open Lean.Meta

/-- -/
def domainEquiv (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  match ← inferType e with
  | Expr.app (Expr.app (Expr.const ``Equiv _) E) D =>
    let lem := mkApp3 (mkConst ``Minimization.domain_equiv) D E e
    let newGoal ← goal.apply lem
    let (newGoal, otherNewGoals) ← match newGoal with
      | List.cons newGoal otherNewGoals => pure (newGoal, otherNewGoals)
      | _ => throwError "unexpected number of subgoals: {← newGoal.mapM (fun m => MVarId.getType m)}"
    let newGoal ← cleanUpComp newGoal
    return newGoal :: otherNewGoals
  | _ => throwError "Given term not of type Equiv"

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Term Lean.Elab.Tactic

syntax (name := domainEquiv) "domain_equiv " term : tactic

/-- -/
@[tactic domainEquiv]
partial def evalDomainEquiv : Tactic := fun stx => match stx with
| `(tactic| domain_equiv $t) => do
  let t ← Term.elabTerm t.raw none
  let goal ← getMainGoal
  replaceMainGoal $ ← Meta.domainEquiv goal t
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
