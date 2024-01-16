import CvxLean.Meta.Minimization

namespace CvxLean

open Lean

open Meta Elab Tactic

namespace Meta

/-- -/
def showVars (goal : MVarId) (p : FVarId) : MetaM MVarId := do
  -- Revert variables after p.
  let (revertedVars, goal) ← MVarId.withContext goal do
    let pDecl ← FVarId.getDecl p
    let fVarIds := (← getLCtx).decls.toArray.filterMap id
      |>.filter (fun decl => decl.index > pDecl.index)
      |>.map LocalDecl.fvarId
    let (_, goal) ← MVarId.revert goal fVarIds
    return (fVarIds, goal)
  -- Introduce new variables and replace them in goal.
  let goal ← MVarId.withContext goal do
    let pDecl ← FVarId.getDecl p
    let domain ← instantiateMVars pDecl.type
    return ← withDomainLocalDecls domain (mkFVar p) fun xs _ => do
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

syntax (name := showVars) "show_vars" ident : tactic

/-- -/
@[tactic showVars]
partial def evalShowVars : Tactic
| `(tactic| show_vars $p) => do
    replaceMainGoal [← Meta.showVars (← getMainGoal) (← withMainContext do getFVarId p)]
| _ => throwUnsupportedSyntax

end Tactic

namespace Tactic.Conv

syntax (name := showVars) "show_vars" ident : conv

/-- Like the basic `show_vars` but as a conv tactic. -/
@[tactic showVars]
partial def evalShowVars : Tactic
| `(conv| show_vars $p) => do
  replaceMainGoal [← Meta.showVars (← getMainGoal) (← withMainContext do getFVarId p)]
| _ => throwUnsupportedSyntax

end Tactic.Conv

end CvxLean
