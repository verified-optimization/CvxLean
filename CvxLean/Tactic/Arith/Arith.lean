import Lean
import Qq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import CvxLean.Tactic.Arith.NormNumVariants
import CvxLean.Tactic.Arith.PositivityExt

/-!
# Arithmetic tactics

This file defines the `positivity!` and `arith` tactics, which are slight extensions of the existing
arithmetic tactics in mathlib (`positivity` and `linarith`).
-/

namespace Tactic

open Lean Meta Elab Tactic Qq

elab (name := cases_and) "cases_and" : tactic => do
  let mvarId ← getMainGoal
  let mvarId' ← mvarId.casesAnd
  replaceMainGoal [mvarId']

/-- Positivity can only work with goals and hypotheses of the form `0 R x`, where `R ∈ {<, ≤, ≠}`.
Our positivity extension is designed to admit hypotheses of the form `a R x` and `x R a` where
`a ≠ 0`. For example, `1 ≤ x → 0 ≤ log x`. To be able to use `positivity`, we rewrite `1 ≤ x` into
`0 ≤ x - 1`. This procedure does exactly that, changing goals and hypotheses to make them compatible
with `positivity`. -/
def preparePositivity (mvarId : MVarId) : MetaM MVarId := do
  mvarId.withContext do
    -- Adjust hypotheses if needed.
    let mut hyps := #[]
    let le_lemmas := [``sub_nonneg_of_le, ``neg_nonneg_of_nonpos]
    let lt_lemmas := [``sub_pos_of_lt, ``neg_pos_of_neg]
    let mut lctx ← getLCtx
    for localDecl in lctx do
      let ty := localDecl.type
      for (le_or_lt, lemmas) in [(``LE.le, le_lemmas), (``LT.lt, lt_lemmas)] do
        let ty := Expr.consumeMData ty
        match ty.app4? le_or_lt with
        | some (R, _, lhs, rhs) =>
            if !(← isDefEq R q(ℝ)) then
              continue
            if ← isDefEq lhs q(0 : ℝ) then
              continue
            let le_or_lt_lemma :=
              if ← isDefEq rhs q(0 : ℝ) then lemmas[1]! else lemmas[0]!
            -- If LHS is not zero, add new hypothesis.
            let val ← mkAppM le_or_lt_lemma #[localDecl.toExpr]
            let ty ← inferType val
            let n := localDecl.userName
            hyps := hyps.push (Hypothesis.mk n ty val)
        | none => continue

    let (_, mvarId) ← mvarId.assertHypotheses hyps

    -- Adjust goal if needed.
    let goalExpr ← mvarId.getType
    let mut mvarId := mvarId
    let le_lemmas := [``le_of_sub_nonneg, ``nonpos_of_neg_nonneg]
    let lt_lemmas := [``lt_of_sub_pos, ``neg_of_neg_pos]
    for (le_or_lt, lemmas) in [(``LE.le, le_lemmas), (``LT.lt, lt_lemmas)] do
      match goalExpr.app4? le_or_lt with
        | some (R, _, lhs, rhs) =>
            if !(← isDefEq R q(ℝ)) then
              continue
            if ← isDefEq lhs q(0 : ℝ) then
              continue
            let le_or_lt_lemma :=
              if ← isDefEq rhs q(0 : ℝ) then lemmas[1]! else lemmas[0]!
            if let [g] ← mvarId.applyConst le_or_lt_lemma then
              mvarId := g
              break
            else
              throwError "`prepare_positivity` failed."
        | none => continue

    return mvarId

elab (name := prepare_positivity) "prepare_positivity" : tactic => do
  let mvarId ← getMainGoal
  let mvarId' ← preparePositivity mvarId
  replaceMainGoal [mvarId']

open Mathlib.Meta.Positivity

/-- Call `positivity` but if the expression has no free variables, we try to apply `norm_num`
first. -/
def positivityMaybeNormNum : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let t : Q(Prop) ← withReducible g.getType'
    let fvs := (collectFVars {} t).fvarSet
    let tac ←
      if fvs.isEmpty then
        `(tactic| (try { norm_num } <;> positivity))
      else
        `(tactic| positivity)
    let [] ← evalTacticAt tac g | throwError "`positivity_maybe_norm_num` failed."

elab (name := positivity) "positivity_maybe_norm_num" : tactic =>
  positivityMaybeNormNum

end Tactic

/-- Extension of `positivity` with some pre-processing and the option to call `norm_num`. -/
syntax "positivity!" : tactic

macro_rules
  | `(tactic| positivity!) =>
    `(tactic| intros; cases_and; prepare_positivity; positivity_maybe_norm_num)

/-- Combination of tactics. We try `positivity!`, then `linarith`, then `norm_num`, then `simp`. -/
syntax "arith" : tactic

macro_rules
  | `(tactic| arith) =>
    `(tactic| (
        try { positivity! } <;> try { linarith } <;> try { norm_num_simp_pow } <;> try { simp }))
