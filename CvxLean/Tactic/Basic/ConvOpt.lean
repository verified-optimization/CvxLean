import CvxLean.Lib.Equivalence
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Basic.ShowVars

namespace CvxLean

open Lean

namespace Tactic.Conv

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta Meta

syntax (name := convObj)
  "conv_obj" "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

syntax (name := convConstr)
  "conv_constr" (ident)? "=>" Lean.Parser.Tactic.Conv.convSeq : tactic

/-- Wrapper function to enter conv mode on an optimization problem. -/
def convertOpt (changeObjFun : Bool) (convTac : TacticM Unit) : EquivalenceBuilder := fun _ g =>
  g.withContext do
    -- Convert to equality goal.
    if let [gEq] ← g.apply (mkConst ``Minimization.Equivalence.ofEq) then
      -- Use `congr` to split objFun and constraints.
      let gs := List.filterMap id <| ← Conv.congr gEq
      if let [objFunGoal, constrsGoal] := gs then
        let gToIgnore := if changeObjFun then constrsGoal else objFunGoal
        let gToChange := if changeObjFun then objFunGoal else constrsGoal
        if let _ :: _ ← evalTacticAt (← `(tactic| rfl)) gToIgnore then
          let failureLocation := if changeObjFun then "constraints" else "objective function"
          throwError "`conv_opt` error: failed to close {failureLocation} subgoals."
        if let [gToConv] ← evalTacticAt (← `(conv| ext $(mkIdent `p))) gToChange then
          if let [gToConv] ← evalTacticAt  (← `(conv| show_vars $(mkIdent `p))) gToConv then
            -- Apply conv tactic.
            for mvarId in ← Tactic.run gToConv convTac do
              liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
          else
            throwError "`conv_opt` error: failed to show optimization variables."
        else
          throwError "`conv_opt` error: failed to close subgoals."
      else
        throwError "`conv_opt` error: unexpected goal type."
    else
      throwError "`conv_opt` error: could not convert to equality goal."

section ConvObj

/-- Enter conv mode on the objective function. -/
def convertObj (conv : TacticM Unit) : EquivalenceBuilder :=
  convertOpt (changeObjFun := true) conv

@[tactic convObj]
partial def evalConvObj : Tactic := fun stx => match stx with
  | `(tactic| conv_obj => $code) => do
      (convertObj (evalTactic code)).toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end ConvObj

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

end Tactic.Conv

end CvxLean
