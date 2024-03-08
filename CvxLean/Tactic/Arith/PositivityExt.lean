import Lean
import Qq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import CvxLean.Lib.Math.Data.Real

/-!
Ad-hoc positivity extensions for particular examples. If `positivity!` fails, then we can try to add
a new lemma here. This approach is not scalable, but is useful as long as we don't have a general
nonlinear arithmetic tactic.
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Real

lemma Real.log_nonneg_of_ge_one {x : ℝ} : 0 ≤ x - 1 → 0 ≤ log x :=
  fun h => Real.log_nonneg (by linarith)

lemma Real.log_pos_of_gt_one {x : ℝ} : 0 < x - 1 → 0 < log x :=
  fun h => Real.log_pos (by linarith)

@[positivity (log (_ : ℝ))]
def evalLog : PositivityExt where eval {_ _α} zα pα e := do
  let (.app _log (x : Q(ℝ))) ←
    withReducible (whnf e) | throwError "not (Real.log x)"
  -- 0 ≤ x - 1 or 0 < x - 1 ?
  match ← core zα pα (q($x - (1 : ℝ)) : Q(ℝ)) with
  | .nonnegative pa =>
      let pa' ← mkAppM ``Real.log_nonneg_of_ge_one #[pa]
      pure (.nonnegative pa')
  | .positive pa =>
      let pa' ← mkAppM ``Real.log_pos_of_gt_one #[pa]
      pure (.positive pa')
  | _ =>
      pure .none

lemma Real.one_sub_one_div_sq_nonneg_of_le_one {x : ℝ} :
    0 < x → 0 ≤ 1 - x → 0 ≤ (1 / x ^ (2 : ℝ)) - 1 :=
  fun h1 h2 => by
    have hx1 : x ≤ 1 := by linarith
    have h0x : 0 ≤ x := by positivity
    have h0x2 : 0 < x ^ (2 : ℝ) := by positivity
    rw [le_sub_iff_add_le, zero_add, le_div_iff h0x2, one_mul]
    simpa [abs_eq_self.mpr h0x]

@[positivity ((1 / (_ : ℝ) ^ (2 : ℝ)) - 1)]
def evalOneDivSqSubOne : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub
    (.app (.app _div _one) (.app (.app _pow (x : Q(ℝ))) _two))) _one') ←
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

lemma Real.one_sub_sq_nonneg_of_le_one {x : ℝ} : 0 ≤ x → 0 ≤ 1 - x → 0 ≤ 1 - x ^ (2 : ℝ) :=
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

lemma Real.scaled_sq_diff_pos_of_pos {a x : ℝ} :
    0 < a - 1 → 0 < x → 0 < (a * x) ^ (2 : ℝ) - x ^ (2 : ℝ) :=
  fun h1 h2 => by
    have ha : 0 ≤ a := by linarith
    have ha1 : 1 < a := by linarith
    have hx : 0 ≤ x := by linarith
    have hx2 : 0 < x ^ (2 : ℝ) := by positivity
    rw [sub_pos, Real.mul_rpow ha hx, ← div_lt_iff hx2, div_self (ne_of_gt hx2)]
    simp [ha1, abs_eq_self.mpr ha]

@[positivity (((_ : ℝ) * (_ : ℝ)) ^ (2 : ℝ)) - ((_ : ℝ) ^ (2 : ℝ))]
def evalSubMulSqSq : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub
    (.app (.app _pow (.app (.app _mul (a : Q(ℝ))) (x : Q(ℝ)))) _two))
    (.app (.app _pow' (x' : Q(ℝ))) _two')) ←
    withReducible (whnf e) | throwError "not ((a * x) ^ 2 - x ^ 2)"
  if !(← isDefEq x x') then
    return .none
  -- 0 < a - 1 ?
  let h1 := ← do
    match ← core zα pα (q($a - 1) : Q(ℝ)) with
    | .positive pa => return some pa
    | _ => return none
  -- 0 < x ?
  let h2 := ← do
    match ← core zα pα x with
    | .positive pa => return some pa
    | _ => return none
  -- If 0 < a - 1 and 0 < x, then 0 < (a * x) ^ 2 - x ^ 2
  match h1, h2 with
  | some h1', some h2' =>
      let pa' ← mkAppM ``Real.scaled_sq_diff_pos_of_pos #[h1', h2']
      pure (.positive pa')
  | _, _ =>
      pure .none

end Mathlib.Meta.Positivity
