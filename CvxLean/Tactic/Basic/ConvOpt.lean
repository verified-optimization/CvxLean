import CvxLean.Lib.Equivalence
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Basic.ShowVars

namespace CvxLean

open Lean

namespace Tactic.Conv

open Meta Elab Parser Tactic Conv

syntax (name := convObj) "conv_obj" "=>" (convSeq)? : tactic

syntax (name := convConstr) "conv_constr" (ident)? "=>" (convSeq)? : tactic

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
          if let [gToConv] ← evalTacticAt (← `(conv| show_vars $(mkIdent `p))) gToConv then
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

/-- Enter conv mode on the objective function. The `shouldEval` flag is set to false when no tactics
are applied but we still want to enter conv mode and see the goal. -/
def convertObj (shouldEval : Bool) (stx : Syntax) : EquivalenceBuilder :=
  convertOpt (changeObjFun := true) do
    if shouldEval then evalTactic stx else saveTacticInfoForToken stx

@[tactic convObj]
partial def evalConvObj : Tactic := fun stx => match stx with
  | `(tactic| conv_obj => $code) => (convertObj true code).toTactic
  -- Avoid errors on empty conv block.
  | `(tactic| conv_obj =>) => do (convertObj false stx).toTactic
  | _ => throwUnsupportedSyntax

end ConvObj

section ConvConstr

/-- Split ands in conv goal. -/
partial def splitAnds (goal : MVarId) : TacticM (List MVarId) := do
  let lhs := (← getLhsRhsCore goal).1
  match lhs with
  | .app (.app (.const ``And _) p) _q => do
      let (mp, mq) ← match List.filterMap id <| ← Conv.congr <| goal with
        | [mp, mq] => pure (mp, mq)
        | _ => throwError "`conv_constr` error: unexpected number of subgoals in `splitAnds`."
      let tag ← getLabelName p
      mp.setTag tag
      return mp :: (← splitAnds mq)
  | _ => do
      let tag ← getLabelName lhs
      goal.setTag tag
      return [goal]

/-- Enter conv mode setting all constraints as subgoals. -/
def convertConstrs (shouldEval : Bool) (stx : Syntax) : EquivalenceBuilder :=
  convertOpt (changeObjFun := false) do
    replaceMainGoal <| ← splitAnds <| ← getMainGoal
    if shouldEval then evalTactic stx else saveTacticInfoForToken stx

/-- Enter conv mode on a specific constraint. -/
def convertConstrWithName (shouldEval : Bool) (stx : Syntax) (h : Name) : EquivalenceBuilder :=
  convertOpt (changeObjFun := false) do
    let constrs ← splitAnds <| ← getMainGoal
    let mut found := false
    for constr in constrs do
      let t ← constr.getTag
      if t == h then
        found := true
        replaceMainGoal [constr]
        if shouldEval then evalTactic stx else saveTacticInfoForToken stx
        -- Ensure that labels are not lost after tactic is applied.
        let g ← getMainGoal
        let (lhs, rhs) ← getLhsRhsCore g
        let lhsWithLabel := mkLabel t lhs
        let eq ← mkEq lhsWithLabel rhs
        let g ← MVarId.replaceTargetEq g eq (← mkEqRefl eq)
        replaceMainGoal [g]
      else
        let gs ← evalTacticAt (← `(tactic| rfl)).raw constr
        if !gs.isEmpty then
          throwError "`conv_constr` error: failed to close all subgoals."
    if !found then
      throwError "`conv_constr` error: no constraint with name {h} found."

@[tactic convConstr]
partial def evalConvConstr : Tactic := fun stx => match stx with
  | `(tactic| conv_constr => $code) => (convertConstrs true code).toTactic
  | `(tactic| conv_constr $h => $code) => (convertConstrWithName true code h.getId).toTactic
  -- Avoid errors on empty conv block.
  | `(tactic| conv_constr =>) => do (convertConstrs false stx).toTactic
  | `(tactic| conv_constr $h =>) => do (convertConstrWithName false stx h.getId).toTactic
  | _ => throwUnsupportedSyntax

end ConvConstr

end Tactic.Conv

end CvxLean
