import Aesop
import CvxLean.Command.Reduction
import CvxLean.Lib.Missing.Real
import CvxLean.Tactic.DCP.Dcp
import CvxLean.Tactic.DCP.AtomLibrary

open CvxLean Minimization

open Lean Meta Elab Tactic Aesop

def isDCP (goal : MVarId) : MetaM Bool := do
  let state ← saveState
  try 
    dbg_trace "DCP?"
    let _ ← DCP.canonizeGoal goal
    dbg_trace "DCP!"
    return true
  catch _ => 
    dbg_trace "not DCP!"
    return false
  finally 
    restoreState state

def closeIfDCP : RuleTac := fun input =>
  input.goal.withContext do
    let lctx ← getLCtx
    if lctx.decls.size == 1 then 
      if let some doneHyp := lctx.decls[0]! then
        if (← isDCP input.goal) then
          let doneId := doneHyp.fvarId
          let state ← saveState
          try 
            input.goal.exact (mkFVar doneId)
            let tac ← `(tactic| exact $(mkIdent $ ← doneId.getUserName))
            let postState ← saveState 
            let scriptBuilder? := mkScriptBuilder? true <| .ofTactic 1 <| 
              withTransparencySyntax TransparencyMode.default <| tac
            let rapp : RuleApplication := ⟨#[], postState, scriptBuilder?⟩ 
            return ⟨#[rapp]⟩ 
          catch _ => 
            return ⟨#[]⟩
          finally restoreState state
    return ⟨#[]⟩

-- Ignore assumptions.
attribute [-aesop] Aesop.BuiltinRules.applyHyps
attribute [-aesop] Aesop.BuiltinRules.assumption

-- Only close with custom rule.
attribute [aesop safe tactic] closeIfDCP


def P : Minimization ℝ ℝ := sorry
def Q : Minimization ℝ ℝ  := sorry 

def R : Minimization ℝ ℝ  := 
  optimization (x : ℝ)
    minimize (x)
    subject to 
      h : 0 ≤ x

@[aesop safe]
lemma pq : Solution Q → Solution P := sorry 

@[aesop safe]
lemma qgood : Solution (optimization (x : ℝ)
    minimize (x)
    subject to 
      h : 0 ≤ x) → Solution Q := sorry

@[aesop safe]
lemma qr : Solution R → Solution P := sorry

section Test

set_option trace.Meta.debug true

reduction red/target : P := by
  aesop?


end Test 

