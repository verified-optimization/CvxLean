import CvxLean.Meta.Equivalence
import CvxLean.Lib.Reduction

/-!
Infrastructure to work with `Reduction` types as expressions. We also define some basic tactics
that work on reduction goals:
* `reduction_rfl` closes a goal by reflexivity.
* `reduction_trans` applies transitivity.
* `reduction_step => ...` allows users to apply one reduction step in the `reduction` command
  by first applying transitivity as otherwise the goal would be closed immediately.
-/

namespace CvxLean

namespace Meta

open Lean Meta

/-- `Reduction` type components as expressions. -/
structure ReductionExpr where
  domainLHS : Expr
  domainRHS : Expr
  codomain : Expr
  codomainLHSreorder : Expr
  lhs : Expr
  rhs : Expr

namespace ReductionExpr

def toMinimizationExprLHS (redExpr : ReductionExpr) : MetaM MinimizationExpr :=
  MinimizationExpr.fromExpr redExpr.lhs

def toMinimizationExprRHS (redExpr : ReductionExpr) : MetaM MinimizationExpr :=
  MinimizationExpr.fromExpr redExpr.rhs

def toExpr (redExpr : ReductionExpr) : Expr :=
  mkApp6 (mkConst ``Minimization.Reduction) redExpr.domainLHS redExpr.domainRHS redExpr.codomain
    redExpr.codomainLHSreorder redExpr.lhs redExpr.rhs

def fromExpr (e : Expr) : MetaM ReductionExpr := do
  match e with
  | .app (.app (.app (.app (.app (.app (.const ``Minimization.Reduction _)
      domainLHS) domainRHS) codomain) codomainLHSreorder) p) q => do
      return ReductionExpr.mk domainLHS domainRHS codomain codomainLHSreorder p q
  | _ => throwError "Expression not of the form `Minimization.Reduction ...`."

def fromGoal (goal : MVarId) : MetaM ReductionExpr := do
  let goalType ← whnf (← MVarId.getDecl goal).type
  fromExpr goalType

end ReductionExpr

macro "reduction_rfl" : tactic => `(tactic| apply Minimization.Reduction.refl)

macro "reduction_trans" : tactic => `(tactic| apply Minimization.Reduction.trans)

open Parser Elab Tactic

elab "reduction_step" _arr:darrow tac:tacticSeqIndentGt : tactic => do
  evalTactic <| ← `(tactic| reduction_trans)
  evalTacticSeq1Indented tac.raw
  if (← getGoals).length > 1 then
    evalTactic <| ← `(tactic| try { reduction_rfl })
  (← getMainGoal).setTag Name.anonymous

end Meta

end CvxLean
