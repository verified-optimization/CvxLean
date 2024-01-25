import CvxLean.Meta.Equivalence
import CvxLean.Lib.Relaxation

namespace CvxLean

namespace Meta

open Lean Meta

/-- `Relaxation` type components as expressions. -/
structure RelaxationExpr where
  domainP : Expr
  domainQ : Expr
  codomain : Expr
  codomainPreorder : Expr
  p : Expr
  q : Expr

namespace RelaxationExpr

def toMinimizationExprLHS (relExpr : RelaxationExpr) : MetaM MinimizationExpr :=
  MinimizationExpr.fromExpr relExpr.p

def toMinimizationExprRHS (relExpr : RelaxationExpr) : MetaM MinimizationExpr :=
  MinimizationExpr.fromExpr relExpr.q

def toExpr (relExpr : RelaxationExpr) : Expr :=
  mkApp6 (mkConst ``Minimization.Relaxation)
    relExpr.domainP relExpr.domainQ relExpr.codomain relExpr.codomainPreorder relExpr.p relExpr.q

def fromExpr (e : Expr) : MetaM RelaxationExpr := do
  match e with
  | .app (.app (.app (.app (.app (.app (.const ``Minimization.Relaxation _)
      domainP) domainQ) codomain) codomainPreorder) p) q => do
      return RelaxationExpr.mk domainP domainQ codomain codomainPreorder p q
  | _ => throwError "Expression not of the form `Minimization.Relaxation ...`."

def fromGoal (goal : MVarId) : MetaM RelaxationExpr := do
  let goalType ← whnf (← MVarId.getDecl goal).type
  fromExpr goalType

end RelaxationExpr

macro "relaxation_rfl" : tactic => `(tactic| apply Minimization.Relaxation.refl)

macro "relaxation_trans" : tactic => `(tactic| apply Minimization.Relaxation.trans)

open Parser Elab Tactic

elab "relaxation_step" _arr:darrow tac:tacticSeqIndentGt : tactic => do
  evalTactic <| ← `(tactic| relaxation_trans)
  evalTacticSeq1Indented tac.raw

end Meta

end CvxLean