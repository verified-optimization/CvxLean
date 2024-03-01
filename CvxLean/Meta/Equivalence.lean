import CvxLean.Meta.Minimization
import CvxLean.Lib.Equivalence

/-!
Infrastructure to work with `Equivalence` types as expressions. We also define some basic tactics
that work on equivalence goals:
* `equivalence_rfl` closes a goal by reflexivity.
* `equivalence_symm` applies symmetry.
* `equivalence_trans` applies transitivity.
* `equivalence_step => ...` allows users to apply one equivalence step in the `equivalence` command
  by first applying transitivity as otherwise the goal would be closed immediately.
-/

namespace CvxLean

open Lean Meta

namespace Meta

/-- `Equivalence` type components as expressions. -/
structure EquivalenceExpr where
  domainLHS : Expr
  domainRHS : Expr
  codomain : Expr
  codomainPreorder : Expr
  lhs : Expr
  rhs : Expr

namespace EquivalenceExpr

def toMinimizationExprLHS (eqvExpr : EquivalenceExpr) : MetaM MinimizationExpr := do
  MinimizationExpr.fromExpr (← whnf eqvExpr.lhs)

def toMinimizationExprRHS (eqvExpr : EquivalenceExpr) : MetaM MinimizationExpr := do
  MinimizationExpr.fromExpr (← whnf eqvExpr.rhs)

def toExpr (eqvExpr : EquivalenceExpr) : Expr :=
  mkApp6 (mkConst ``Minimization.Equivalence) eqvExpr.domainLHS eqvExpr.domainRHS eqvExpr.codomain
    eqvExpr.codomainPreorder eqvExpr.lhs eqvExpr.rhs

def fromExpr (e : Expr) : MetaM EquivalenceExpr := do
  match e with
  | .app (.app (.app (.app (.app (.app (.const ``Minimization.Equivalence _)
      domainLHS) domainRHS) codomain) codomainPreorder) lhs) rhs => do
      return EquivalenceExpr.mk domainLHS domainRHS codomain codomainPreorder lhs rhs
  | _ => throwError "Expression not of the form `Minimization.Equivalence ...`."

def fromGoal (goal : MVarId) : MetaM EquivalenceExpr := do
  let goalType ← whnf (← MVarId.getDecl goal).type
  fromExpr goalType

end EquivalenceExpr

section BasicTactics

macro "equivalence_rfl" : tactic => `(tactic| apply Minimization.Equivalence.refl)

macro "equivalence_symm" : tactic => `(tactic| apply Minimization.Equivalence.symm)

macro "equivalence_trans" : tactic => `(tactic| apply Minimization.Equivalence.trans)

open Parser Elab Tactic

elab "equivalence_step" _arr:darrow tac:tacticSeqIndentGt : tactic => do
  evalTactic <| ← `(tactic| equivalence_trans)
  evalTacticSeq1Indented tac.raw
  if (← getGoals).length > 1 then
    evalTactic <| ← `(tactic| try { equivalence_rfl })
  (← getMainGoal).setTag Name.anonymous

end BasicTactics

end Meta

end CvxLean
