import Lean
import Qq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace Tactic

open Lean Meta Elab Tactic Qq

elab (name := cases_and) "cases_and" : tactic => do
  let mvarId ← getMainGoal
  let mvarId' ← mvarId.casesAnd
  replaceMainGoal [mvarId']

def preparePositivity (mvarId : MVarId) : MetaM MVarId := do
  mvarId.withContext do
    let mut hyps := #[]
    let mut lctx ← getLCtx
    for localDecl in lctx do
      let ty := localDecl.type
      let le_lemma := ``sub_nonneg_of_le
      let lt_lemma := ``sub_pos_of_lt
      for (le_or_lt, le_or_lt_lemma) in [(``LE.le, le_lemma), (``LT.lt, lt_lemma)] do
        let ty := Expr.consumeMData ty
        match ty.app4? le_or_lt with
        | some (R, _, lhs, _rhs) =>
            if ← isDefEq R q(ℝ) then
              if ← isDefEq lhs q(0 : ℝ) then
                continue
              -- If LHS is not zero, add new hypothesis.
              let val ← mkAppM le_or_lt_lemma #[localDecl.toExpr]
              let ty ← inferType val
              let n := localDecl.userName
              hyps := hyps.push (Hypothesis.mk n ty val)
        | none => continue

    let (_, newMVarId) ← mvarId.assertHypotheses hyps
    return newMVarId

elab (name := prepare_positivity) "prepare_positivity" : tactic => do
  let mvarId ← getMainGoal
  let mvarId' ← preparePositivity mvarId
  replaceMainGoal [mvarId']

end Tactic

syntax "positivity_ext" : tactic

macro_rules
  | `(tactic| positivity_ext) =>
    `(tactic| cases_and; prepare_positivity; positivity)
