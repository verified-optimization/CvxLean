-- import CvxLean.Lib.Minimization

-- namespace CvxLean

-- open Lean

-- namespace Tactic.Conv

-- open Lean.Elab Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta Meta

-- syntax (name := convObj)
--   "conv_obj" "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

-- syntax (name := convConstr)
--   "conv_constr" (ident)? "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

-- /-- Wrapper function to enter conv mode on an optimization problem. -/
-- def convertOpt (goal : MVarId) (changeObjFun : Bool) (convTac : TacticM Unit) :
--   TacticM MVarId := do
--   -- Check if goal is actually an optimization problem.
--   let _ ← SolutionExpr.fromGoal goal
--   let target ← MVarId.getType goal
--   let (targetNew, proof) ← convert target do
--     -- Use `congr` to get rid of `Solution`.
--     replaceMainGoal <| List.filterMap id <| ← Conv.congr <| ← getMainGoal
--     -- Use `congr` to split objFun and constraints.
--     replaceMainGoal <| List.filterMap id <| ← Conv.congr <| ← getMainGoal
--     if let [objFunGoal, constrsGoal] ← getGoals then
--       let toIgnore := if changeObjFun then constrsGoal else objFunGoal
--       let toChange := if changeObjFun then objFunGoal else constrsGoal
--       if let [] ← evalTacticAt (← `(tactic| rfl)).raw toIgnore then
--         replaceMainGoal [toChange]
--       else
--         throwError "conv_opt error: Failed to close subgoals."
--       evalTactic (← `(conv| ext $(mkIdent `p))).raw
--       conv
--     else
--       throwError "conv_opt error: Unexpected goal type."
--   let goal ← MVarId.replaceTargetEq goal targetNew proof
--   let goal ←
--     match ← evalTacticAt (← `(tactic| try rfl)).raw goal with
--     | [goal] => return goal
--     | _ => throwError "conv_opt error: Unexpected number of subgoals."
--   return goal

-- section ConvObj

-- /-- Enter conv mode on the objective function. -/
-- partial def convertObj (goal : MVarId) (conv : TacticM Unit) :
--   TacticM MVarId := do
--   convertOpt goal (changeObjFun := true) do
--     replaceMainGoal <| [← getMainGoal]
--     conv

-- @[tactic convObj]
-- partial def evalConvObj : Tactic := fun stx => match stx with
--   | `(tactic| conv_obj => $code) => do
--     replaceMainGoal [← convertObj (← getMainGoal) do evalTactic code.raw]
--   | _ => throwUnsupportedSyntax

-- end ConvObj

-- section ConvConstr

-- /-- Split ands in conv goal. -/
-- partial def splitAnds (goal : MVarId) : TacticM (List MVarId) := do
--   let lhs := (← getLhsRhsCore goal).1
--   match lhs with
--   | Expr.app (Expr.app (Expr.const ``And _) p) _q => do
--     let (mp, mq) ← match List.filterMap id <| ← Conv.congr <| goal with
--       | [mp, mq] => pure (mp, mq)
--       | _ => throwError ("conv_constr error: Unexpected number of subgoals " ++
--           "in splitAnds.")
--     let tag ← getLabelName p
--     mp.setTag tag
--     return mp :: (← splitAnds mq)
--   | _ => do
--     let tag ← getLabelName lhs
--     goal.setTag tag
--     return [goal]

-- /-- Enter conv mode setting all constraints as subgoals. -/
-- partial def convertConstr (goal : MVarId) (conv : TacticM Unit) :
--   TacticM MVarId := do
--   convertOpt goal (changeObjFun := false) do
--     replaceMainGoal <| ← splitAnds <| ← getMainGoal
--     conv

-- /-- Enter conv mode on a specific constraint. -/
-- partial def convertConstrWithName (h : Name) (goal : MVarId)
--   (conv : TacticM Unit) : TacticM MVarId := do
--   convertOpt goal (changeObjFun := false) do
--     let constrs ← splitAnds <| ← getMainGoal
--     let mut found := false
--     for constr in constrs do
--       let t ← constr.getTag
--       if t == h then
--         found := true
--         replaceMainGoal [constr]
--         conv
--         -- Ensure that labels are not lost after tactic is applied.
--         let g ← getMainGoal
--         let (lhs, rhs) ← getLhsRhsCore g
--         let lhsWithLabel := mkLabel t lhs
--         let eq ← mkEq lhsWithLabel rhs
--         let g ← MVarId.replaceTargetEq g eq (← mkEqRefl eq)
--         replaceMainGoal [g]
--       else
--         let gs ← evalTacticAt (← `(tactic| rfl)).raw constr
--         if !gs.isEmpty then
--           throwError "conv_constr error: Failed to close all subgoals."
--     if !found then
--       throwError "conv_constr error: No constraint with name {h} found."

-- @[tactic convConstr]
-- partial def evalConvConstr : Tactic := fun stx => match stx with
--   | `(tactic| conv_constr => $code) => do
--       replaceMainGoal [← convertConstr (← getMainGoal) do evalTactic code.raw]
--   | `(tactic| conv_constr $h => $code) => do
--       replaceMainGoal
--         [← convertConstrWithName h.getId (← getMainGoal) do evalTactic code.raw]
--   | _ => throwUnsupportedSyntax

-- end ConvConstr

-- end Tactic.Conv

-- end CvxLean
