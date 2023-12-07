import Lean
import Qq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import CvxLean.Lib.Math.Data.Real

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

lemma Real.one_sub_one_div_sq_nonneg_of_le_one {x : ℝ} :
  0 < x → 0 ≤ 1 - x → 0 ≤ (1 / x ^ 2) - 1 :=
  fun h1 h2 => by
    have hx1 : x ≤ 1 := by linarith
    have h0x : 0 ≤ x := by positivity
    have h0x2 : 0 < x ^ 2 := by positivity
    rw [le_sub_iff_add_le, zero_add, le_div_iff h0x2, one_mul]
    simpa [abs_eq_self.mpr h0x]

@[positivity ((1 / (_ : ℝ) ^ (2 : ℝ)) - 1)]
def evalOneDivSqSubOne : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub (.app (.app _div _one) (.app (.app _pow (x : Q(ℝ))) _two))) _one') ←
    withReducible (whnf e) | throwError "not ((1 / x ^ 2) - 1)"
  -- 0 < x ?
  let h1 :=
    match ← core zα pα x with
    | .positive pa => some pa
    | _ => none
  -- 0 ≤ 1 - x ?
  let h2 := ← do
    match ← core zα pα (q((1 : ℝ) - $x) : Q(ℝ)) with
    | .nonnegative pa => return some pa
    | .positive pa =>
        let pa ← mkAppM ``le_of_lt #[pa]
        return some pa
    | _ => return none
  -- If 0 < x and 0 ≤ 1 - x, then 0 ≤ (1 / x ^ 2) - 1
  match h1, h2 with
  | some h1', some h2' =>
      let pa' ← mkAppM ``Real.one_sub_one_div_sq_nonneg_of_le_one #[h1', h2']
      pure (.nonnegative pa')
  | _, _ =>
      pure .none

lemma Real.one_sub_sq_nonneg_of_le_one {x : ℝ} :
  0 ≤ x → 0 ≤ 1 - x → 0 ≤ 1 - x ^ (2 : ℝ) :=
  fun h1 h2 => by
    have hx1 : x ≤ 1 := by linarith
    rw [le_sub_iff_add_le, zero_add]
    simpa [abs_eq_self.mpr h1]

@[positivity (1 - ((_ : ℝ) ^ (2 : ℝ)))]
def evalOneSubSq : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub _one) (.app (.app _pow (x : Q(ℝ))) _two)) ←
    withReducible (whnf e) | throwError "not (1 - x ^ 2)"
  -- 0 ≤ x ?
  let h1 := ← do
    match ← core zα pα x with
    | .nonnegative pa => return some pa
    | .positive pa =>
        let pa ← mkAppM ``le_of_lt #[pa]
        return some pa
    | _ => return none
  -- 0 ≤ 1 - x ?
  let h2 := ← do
    match ← core zα pα (q((1 : ℝ) - $x) : Q(ℝ)) with
    | .nonnegative pa => return some pa
    | .positive pa =>
        let pa ← mkAppM ``le_of_lt #[pa]
        return some pa
    | _ => return none
  -- If 0 ≤ x and 0 ≤ 1 - x, then 0 ≤ 1 - x ^ 2
  match h1, h2 with
  | some h1', some h2' =>
      let pa' ← mkAppM ``Real.one_sub_sq_nonneg_of_le_one #[h1', h2']
      pure (.nonnegative pa')
  | _, _ =>
      pure .none

lemma Real.exp_sub_one_pos_of_pos {x : ℝ} : 0 < x → 0 < Real.exp x - 1 :=
  fun h => by simp [h]

@[positivity ((Real.exp (_ : ℝ)) - 1)]
def evalExpSubOne : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub (.app _exp (x : Q(ℝ)))) _one) ←
    withReducible (whnf e) | throwError "not (Real.exp x - 1)"
  match ← core zα pα x with
  | .positive pa =>
      let pa' ← mkAppM ``Real.exp_sub_one_pos_of_pos #[pa]
      pure (.positive pa')
  | _ =>
      pure .none

lemma Real.one_sub_div_exp_pos_of_pos {x : ℝ} : 0 < x → 0 < 1 - 1 / Real.exp x :=
  fun h => by field_simp; positivity

@[positivity (1 - (1 / (Real.exp (_ : ℝ))))]
def evalOneSubDivExp : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub _one) (.app (.app _div _one') (.app _exp (x : Q(ℝ))))) ←
    withReducible (whnf e) | throwError "not (1 - 1 / Real.exp x)"
  match ← core zα pα x with
  | .positive pa =>
      let pa' ← mkAppM ``Real.one_sub_div_exp_pos_of_pos #[pa]
      pure (.positive pa')
  | _ =>
      pure .none

end Mathlib.Meta.Positivity
