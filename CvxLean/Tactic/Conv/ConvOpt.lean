import CvxLean.Lib.Minimization
import CvxLean.Tactic.Conv.ShowVars

namespace CvxLean

open Lean

namespace Tactic.Conv

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta Meta

-- syntax (name := convOpt) 
--   "conv_opt" "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

syntax (name := convObj) 
  "conv_obj" "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

syntax (name := convConstr) 
  "conv_constr" (ident)? "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

/-- -/
-- NOTE(AB): This cannot be written as Meta because convert is not Meta...
-- NOTE(RFM): Are user's ever supposed to use this tactic directly?
def convertOpt (goal : MVarId) (conv : TacticM Unit) : TacticM MVarId := do
   let target ← MVarId.getType goal
   let (targetNew, proof) ← convert target do
     -- TODO: Check if goal is actually an optimization problem.
     -- NOTE(RFM): Why is the goal replaced twice?
     replaceMainGoal <| List.filterMap id <| ← Conv.congr <| ← getMainGoal
     replaceMainGoal <| List.filterMap id <| ← Conv.congr <| ← getMainGoal
     evalTactic (← `(tactic| rfl)).raw
     evalTactic (← `(conv| ext $(mkIdent `p))).raw
     evalTactic (← `(conv| show_vars $(mkIdent `p))).raw
     conv
   let goal ← MVarId.replaceTargetEq goal targetNew proof
   let goal ←
      match ← evalTacticAt (← `(tactic| try rfl)).raw goal with
      | [goal] => return goal
      | _ => throwError "Unexpected number of subgoals in convertOpt."
   return goal

-- @[tactic convOpt]
-- partial def evalConvOpt : Tactic := fun stx => match stx with
-- | `(tactic| conv_opt => $code) => do
--   replaceMainGoal [← convertOpt (← getMainGoal) do evalTactic code.raw]
-- | _ => throwUnsupportedSyntax

/-- Split ands in conv goal. -/
partial def splitAnds (goal : MVarId) : TacticM (List MVarId) := do
  let lhs := (← getLhsRhsCore goal).1
  match lhs with
  | Expr.app (Expr.app (Expr.const ``And _) p) _q => do
    let (mp, mq) ← match List.filterMap id <| ← Conv.congr <| goal with
      | [mp, mq] => pure (mp, mq)
      | _ => throwError "Unexpected number of subgoals in splitAnds."
    dbg_trace s!"{← getLabelName p}"
    let tag ← getLabelName p
    mp.setTag tag
    return mp :: (← splitAnds mq)
  | _ => do 
    dbg_trace s!"{← getLabelName lhs}"
    let tag ← getLabelName lhs 
    goal.setTag tag
    return [goal]

/-- Enter conv mode setting all constraints as subgoals. -/
partial def convertConstr (goal : MVarId) (conv : TacticM Unit) : 
  TacticM MVarId := do
  convertOpt goal do
    replaceMainGoal <| ← splitAnds <| ← getMainGoal 
    conv

/-- Enter conv mode on a specific constraint. -/
partial def convertConstrWithName (h : Name) (goal : MVarId) 
  (conv : TacticM Unit) : TacticM MVarId := do
  convertOpt goal do
    let constrs ← splitAnds <| ← getMainGoal 
    let mut found := false
    for constr in constrs do 
      let t ← constr.getTag
      if t == h then 
        found := true
        replaceMainGoal [constr]
        conv
        -- NOTE(RFM): Ensure that labels are not lost after tactic is applied.
        let g ← getMainGoal 
        let (lhs, rhs) ← getLhsRhsCore g 
        let lhsWithLabel := mkLabel t lhs
        let eq ← mkEq lhsWithLabel rhs
        let g ← MVarId.replaceTargetEq g eq (← mkEqRefl eq)
        replaceMainGoal [g]
      else
        let gs ← evalTacticAt (← `(tactic| rfl)).raw constr 
        if !gs.isEmpty then
          throwError "conv_constr error: Failed to close all subgoals."
    if !found then 
      throwError "conv_constr error: No constraint with name {h} found."

@[tactic convConstr]
partial def evalConvConstr : Tactic := fun stx => match stx with
  | `(tactic| conv_constr => $code) => do
      replaceMainGoal [← convertConstr (← getMainGoal) do evalTactic code.raw]
  | `(tactic| conv_constr $h => $code) => do 
      replaceMainGoal 
        [← convertConstrWithName h.getId (← getMainGoal) do evalTactic code.raw]
  | _ => throwUnsupportedSyntax

end Tactic.Conv

end CvxLean
