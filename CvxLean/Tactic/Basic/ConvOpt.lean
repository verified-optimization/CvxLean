import CvxLean.Lib.Equivalence
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Basic.ShowVars

/-!
# Conversion mode

This file defines the `conv_opt`, `conv_obj`, and `conv_constr` tactics. These tactics are used to
travel to the the component of the optimization problem that we want to modify.
-/

namespace CvxLean

open Lean

namespace Tactic.Conv

open Meta Elab Parser Tactic Conv

/-- Convert whole optimization problem. An optimization problem `p` may appear in the goal in the
following forms: `⊢ Solution p`, `⊢ p ≡ q`, `⊢ p ≼ q`, or `⊢ p ≽' q`. Applying `conv_opt` travels
down to `p` and turns the goal into `| p`. -/
syntax (name := convOpt) "conv_opt" "=>" (convSeq)? : tactic

/-- Following from the comment on `conv_opt`, if `p := ⟨f, cs⟩`, turn the goal into `| f(x)`. -/
syntax (name := convObj) "conv_obj" "=>" (convSeq)? : tactic

/-- Following from the comment on `conv_opt`, if `p := ⟨f, cs⟩`, and `cs(x) := cs₁(x) ∧ ⋯ ∧ csₙ(x)`,
find constraint `csᵢ` with the given tag and turn the goal into `| csᵢ(x)`. -/
syntax (name := convConstr) "conv_constr" (ident)? "=>" (convSeq)? : tactic

/-- Wrapper function to enter conv mode on an optimization problem.
* If `fullProb` is set, then we enter conv mode on the whole problem.
* If `changeObjFun` is set, then we enter conv mode on the objective function.
* Otherwise, we enter `conv` mode on the constraints. -/
def convertOpt (fullProb changeObjFun : Bool := false) (convTac : TacticM Unit) :
    EquivalenceBuilder :=
  fun _ g => g.withContext do
    -- Turn into equality goal.
    if let [gEq] ← g.apply (mkConst ``Minimization.Equivalence.ofEq) then
      -- Choose goal to convert.
      let gToConv ← do
        if fullProb then
          markAsConvGoal gEq
        else
          -- Use `congr` to split objFun and constraints.
          let gs := List.filterMap id <| ← Conv.congr gEq
          if let [objFunGoal, constrsGoal] := gs then
            let gToIgnore := if changeObjFun then constrsGoal else objFunGoal
            let gToChange := if changeObjFun then objFunGoal else constrsGoal
            if let _ :: _ ← evalTacticAt (← `(tactic| rfl)) gToIgnore then
              let failureLocation := if changeObjFun then "constraints" else "objective function"
              throwConvOptError "failed to close {failureLocation} subgoals."
            else
            -- Introduce optimization variables.
            if let [gToConv] ← evalTacticAt (← `(conv| ext $(mkIdent `p))) gToChange then
              if let [gToConv] ← evalTacticAt (← `(conv| show_vars $(mkIdent `p))) gToConv then
                pure gToConv
              else
                throwConvOptError "failed to show optimization variables."
            else
              throwConvOptError "failed to introduce optimization variables."
          else
            throwConvOptError "unexpected goal type."

      -- Apply `conv` tactic.
      for mvarId in ← Tactic.run gToConv convTac do
        liftM <| mvarId.refl <|> mvarId.inferInstance <|> pure ()
    else
      throwConvOptError "could not convert to equality goal."

/-- Enter `conv` mode on the full problem. The `shouldEval` flag is set to false when no tactics are
applied but we still want to enter conv mode and see the goal. -/
def convertFullProb (shouldEval : Bool) (stx : Syntax) : EquivalenceBuilder :=
  convertOpt (fullProb := true) (changeObjFun := false) do
    if shouldEval then evalTactic stx else saveTacticInfoForToken stx

@[tactic convOpt]
partial def evalConvOpt : Tactic := fun stx => match stx with
  | `(tactic| conv_opt => $code) => (convertFullProb true code).toTactic
  -- Avoid errors on empty `conv` block.
  | `(tactic| conv_opt =>) => do (convertFullProb false stx).toTactic
  | _ => throwUnsupportedSyntax

section ConvObj

/-- Enter `conv` mode on the objective function. -/
def convertObj (shouldEval : Bool) (stx : Syntax) : EquivalenceBuilder :=
  convertOpt (fullProb := false) (changeObjFun := true) do
    if shouldEval then evalTactic stx else saveTacticInfoForToken stx

@[tactic convObj]
partial def evalConvObj : Tactic := fun stx => match stx with
  | `(tactic| conv_obj => $code) => (convertObj true code).toTactic
  -- Avoid errors on empty `conv` block.
  | `(tactic| conv_obj =>) => (convertObj false stx).toTactic
  | _ => throwUnsupportedSyntax

end ConvObj

section ConvConstr

/-- Split ands in `conv` goal. -/
partial def splitAnds (goal : MVarId) : TacticM (List MVarId) := do
  let lhs := (← getLhsRhsCore goal).1
  match lhs with
  | .app (.app (.const ``And _) p) _q => do
      let (mp, mq) ← match List.filterMap id <| ← Conv.congr <| goal with
        | [mp, mq] => pure (mp, mq)
        | _ => throwConvConstrError "unexpected number of subgoals in `splitAnds`."
      let tag ← getLabelName p
      mp.setTag tag
      return mp :: (← splitAnds mq)
  | _ => do
      let tag ← getLabelName lhs
      goal.setTag tag
      return [goal]

/-- Enter `conv` mode setting all constraints as subgoals. -/
def convertConstrs (shouldEval : Bool) (stx : Syntax) : EquivalenceBuilder :=
  convertOpt (fullProb := false) (changeObjFun := false) do
    replaceMainGoal <| ← splitAnds <| ← getMainGoal
    if shouldEval then evalTactic stx else saveTacticInfoForToken stx

/-- Enter `conv` mode on a specific constraint. -/
def convertConstrWithName (shouldEval : Bool) (stx : Syntax) (h : Name) : EquivalenceBuilder :=
  convertOpt (fullProb := false) (changeObjFun := false) do
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
          throwConvConstrError "failed to close all subgoals."
    if !found then
      throwConvConstrError "no constraint with name {h} found."

@[tactic convConstr]
partial def evalConvConstr : Tactic := fun stx => match stx with
  | `(tactic| conv_constr => $code) => (convertConstrs true code).toTactic
  | `(tactic| conv_constr $h => $code) => (convertConstrWithName true code h.getId).toTactic
  -- Avoid errors on empty `conv` block.
  | `(tactic| conv_constr =>) => (convertConstrs false stx).toTactic
  | `(tactic| conv_constr $h =>) => (convertConstrWithName false stx h.getId).toTactic
  | _ => throwUnsupportedSyntax

end ConvConstr

end Tactic.Conv

end CvxLean
