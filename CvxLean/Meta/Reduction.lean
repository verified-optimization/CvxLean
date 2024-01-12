import CvxLean.Meta.Equivalence
import CvxLean.Lib.Reduction

namespace CvxLean

namespace Meta

open Lean Meta

/-- `Reduction` type components as expressions. -/
structure ReductionExpr where
  domainP : Expr
  domainQ : Expr
  codomain : Expr
  codomainPreorder : Expr
  p : Expr
  q : Expr

namespace ReductionExpr

def toMinimizationExprLHS (redExpr : ReductionExpr) : MetaM MinimizationExpr :=
  MinimizationExpr.fromExpr redExpr.p

def toMinimizationExprRHS (redExpr : ReductionExpr) : MetaM MinimizationExpr :=
  MinimizationExpr.fromExpr redExpr.q

def toExpr (redExpr : ReductionExpr) : Expr :=
  mkApp6 (mkConst ``Minimization.Reduction)
    redExpr.domainP redExpr.domainQ redExpr.codomain redExpr.codomainPreorder redExpr.p redExpr.q

def fromExpr (e : Expr) : MetaM ReductionExpr := do
  match e with
  | .app (.app (.app (.app (.app (.app (.const ``Minimization.Reduction _)
      domainP) domainQ) codomain) codomainPreorder) p) q => do
      return ReductionExpr.mk domainP domainQ codomain codomainPreorder p q
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

end Meta

end CvxLean
