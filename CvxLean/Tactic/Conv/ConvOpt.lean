import CvxLean.Lib.Minimization
import CvxLean.Tactic.Conv.ShowVars

attribute [-instance] coeDecidableEq

namespace CvxLean

open Lean

namespace Tactic.Conv

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta Meta

syntax (name := convOpt) "conv_opt" "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

syntax (name := convConstr) "conv_constr" "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

/-- -/
-- TODO: This cannot be written as Meta because convert is not Meta...
def convertOpt (goal : MVarId) (conv : TacticM Unit) : TacticM MVarId := do
   let target ← MVarId.getType goal
   let (targetNew, proof) ← convert target do
     --TODO: Check if goal is actually an optimization problem.
     replaceMainGoal $ List.filterMap id $ ← Conv.congr $ ← getMainGoal
     replaceMainGoal $ List.filterMap id $ ← Conv.congr $ ← getMainGoal
     evalTactic (← `(tactic| rfl)).raw
     evalTactic (← `(conv| ext $(mkIdent `p))).raw
     evalTactic (← `(conv| show_vars $(mkIdent `p))).raw
     conv
   let goal ← MVarId.replaceTargetEq goal targetNew proof
   let goal ←
      match ← evalTacticAt (← `(tactic| try rfl)).raw goal with
      | [goal] => return goal
      | _ => throwError "Unexpected number of subgoals"
   return goal

/-- -/
@[tactic convOpt]
partial def evalConvOpt : Tactic := fun stx => match stx with
| `(tactic| conv_opt => $code) => do
  replaceMainGoal [← convertOpt (← getMainGoal) do evalTactic code.raw]
| _ => throwUnsupportedSyntax

/-- -/
partial def convertConstr (goal : MVarId) (conv : TacticM Unit) : TacticM MVarId := do
  let goal ← convertOpt goal do
    replaceMainGoal $ ← splitAnds $ ← getMainGoal
    conv
  return goal
where 
  splitAnds (goal : MVarId) : TacticM (List MVarId) := do
    let lhs := (← getLhsRhsCore goal).1
    match lhs with
    | Expr.app (Expr.app (Expr.const ``And _) p) q => do
      let (mp, mq) ← match List.filterMap id $ ← Conv.congr $ goal with
        | [mp, mq] => pure (mp, mq)
        | _ => throwError "Unexpected number of subgoals"
      mp.setTag (← getLabelName p)
      return mp :: (← splitAnds mq)
    | _ => do 
      goal.setTag (← getLabelName lhs)
      return [goal]

/-- -/
@[tactic convConstr]
partial def evalConvConstr : Tactic := fun stx => match stx with
| `(tactic| conv_constr => $code) => do
  replaceMainGoal [← convertConstr (← getMainGoal) do evalTactic code.raw]
| _ => throwUnsupportedSyntax

end Tactic.Conv

end CvxLean
