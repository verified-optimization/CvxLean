import CvxLean.Meta.Minimization
import CvxLean.Lib.Equivalence

namespace CvxLean

namespace Meta

open Lean Meta

/-- `Equivalence` type components as expressions. -/
structure EquivalenceExpr where
  domainP : Expr
  domainQ : Expr
  codomain : Expr
  codomainPreorder : Expr
  p : Expr
  q : Expr

namespace EquivalenceExpr

def toMinimizationExprLHS (eqvExpr : EquivalenceExpr) : MetaM MinimizationExpr := do
  MinimizationExpr.fromExpr (← whnf eqvExpr.p)

def toMinimizationExprRHS (eqvExpr : EquivalenceExpr) : MetaM MinimizationExpr := do
  MinimizationExpr.fromExpr (← whnf eqvExpr.q)

def toExpr (eqvExpr : EquivalenceExpr) : Expr :=
  mkApp6 (mkConst ``Minimization.Equivalence)
    eqvExpr.domainP eqvExpr.domainQ eqvExpr.codomain eqvExpr.codomainPreorder eqvExpr.p eqvExpr.q

def fromExpr (e : Expr) : MetaM EquivalenceExpr := do
  match e with
  | .app (.app (.app (.app (.app (.app (.const ``Minimization.Equivalence _)
      domainP) domainQ) codomain) codomainPreorder) p) q => do
      return EquivalenceExpr.mk domainP domainQ codomain codomainPreorder p q
  | _ => throwError "Expression not of the form `Minimization.Equivalence ...`."

def fromGoal (goal : MVarId) : MetaM EquivalenceExpr := do
  let goalType ← whnf (← MVarId.getDecl goal).type
  fromExpr goalType

end EquivalenceExpr

macro "equivalence_rfl" : tactic => `(tactic| apply Minimization.Equivalence.refl)

macro "equivalence_symm" : tactic => `(tactic| apply Minimization.Equivalence.symm)

macro "equivalence_trans" : tactic => `(tactic| apply Minimization.Equivalence.trans)

open Parser Elab Tactic

elab "equivalence_step" _arr:darrow tac:tacticSeqIndentGt : tactic => do
  evalTactic <| ← `(tactic| equivalence_trans)
  evalTacticSeq1Indented tac.raw

end Meta

end CvxLean
