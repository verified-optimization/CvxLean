import Lean
import CvxLean.Meta.Minimization

namespace Lean.LocalContext

/-- -/
def getDecls (lctx : LocalContext) : Array LocalDecl :=
  lctx.decls.foldl (init := #[]) fun r decl? => match decl? with
    | some decl => r.push decl
    | none      => r

end Lean.LocalContext

namespace CvxLean

open Lean

namespace Meta

open Lean.Meta Lean.Elab.Tactic

/-- -/
def showVars (goal : MVarId) (p : FVarId) : MetaM MVarId := do
  -- Revert variables after p.
  let (revertedVars, goal) ← MVarId.withContext goal do
    let pDecl ← FVarId.getDecl p
    let fVarIds := (← getLCtx).getDecls
      |>.filter (fun decl => decl.index > pDecl.index)
      |>.map LocalDecl.fvarId
    let (_, goal) ← MVarId.revert goal fVarIds
    return (fVarIds, goal)
  -- Introduce new variables and replace them in goal.
  let goal ← MVarId.withContext goal do
    let pDecl ← FVarId.getDecl p
    let domain ← instantiateMVars pDecl.type
    return ← withDomainLocalDecls domain (mkFVar p) fun xs prs => do
      let target ← instantiateMVars (← MVarId.getDecl goal).type
      let newTarget ← Meta.replaceProjections target p xs
      let mVar ← mkFreshExprMVar newTarget MetavarKind.syntheticOpaque
      MVarId.assign goal (← mkLetFVars xs mVar)
      return mVar.mvarId!
  -- Reintroduce reverted variables.
  let (_, goal) ← MVarId.introNP goal revertedVars.size
  return goal

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := showVars) "show_vars" ident : tactic

/-- -/
@[tactic showVars]
partial def evalShowVars : Tactic
| `(tactic| show_vars $p) => do
  replaceMainGoal [← Meta.showVars (← getMainGoal) (← withMainContext do getFVarId p)]
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
