import CvxLean.Lib.Minimization
import CvxLean.Meta.Minimization

namespace CvxLean

namespace Meta

open Lean Lean.Meta

/-- -/
def replaceConstr (goal : MVarId) : MetaM (MVarId × MVarId × MVarId) := MVarId.withContext goal do
  let goalExprs ← matchSolutionExpr goal
    
  -- New Constraints.
  let newConstr ← mkFreshExprMVar (some $ ← mkArrow goalExprs.domain' (mkSort levelZero))
  let newTarget := {goalExprs with constraints := newConstr}.toExpr
  let newGoal ← mkFreshExprSyntheticOpaqueMVar newTarget

  let p ← mkFreshFVarId
  let lctx := (← getLCtx).mkLocalDecl p `p goalExprs.domain' Lean.BinderInfo.default

  let eqTarget ← 
    withReader (fun ctx => { ctx with lctx := lctx }) do
      let constraintsBody := goalExprs.constraints.bindingBody!.instantiate1 (mkFVar p)
      let newConstrBody := mkApp newConstr (mkFVar p)
      let eqTarget ← mkEq constraintsBody newConstrBody
      let eqTarget ← mkForallFVars #[mkFVar p] eqTarget
      return eqTarget
  let eqGoal ← mkFreshExprSyntheticOpaqueMVar eqTarget
  let eq ← mkFunExt eqGoal
  let eq ← mkCongrArg 
    (mkApp3 (mkConst ``Minimization.mk) goalExprs.domain' goalExprs.codomain' goalExprs.objFun)
    eq
  let eq ← mkCongrArg 
    (mkApp3 (mkConst ``Minimization.Solution) goalExprs.domain goalExprs.codomain goalExprs.codomainPreorder)
    eq
  MVarId.assign goal $ ← mkEqMPR eq newGoal
  return (newConstr.mvarId!, eqGoal.mvarId!, newGoal.mvarId!)

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := replaceConstrCore) "replace_constr_core" : tactic

@[tactic replaceConstrCore]
partial def evalReplaceConstrCore : Tactic := fun stx => match stx with
| `(tactic| replace_constr_core) => do
  let (g1, g2, g3) ← Meta.replaceConstr (← getMainGoal)
  replaceMainGoal [g1, g2, g3]
| _ => throwUnsupportedSyntax

macro "replace_constr" t:term : tactic => `(tactic| { replace_constr_core; exact $t })

end Tactic

end CvxLean
