import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Test.Util.TimeCmd

-- TODO: Move.
lemma Real.one_sub_one_div_sq_nonneg_of_one_le {x : ℝ} :
  0 < x → 0 ≤ 1 - x → 0 ≤ (1 / x ^ 2) - 1 :=
  fun h1 h2 => by
    have hx1 : x ≤ 1 := by linarith
    have h0x : 0 ≤ x := by positivity
    have h0x2 : 0 < x ^ 2 := by positivity
    rw [le_sub_iff_add_le, zero_add, le_div_iff h0x2, one_mul]
    simpa [abs_eq_self.mpr h0x]

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

@[positivity ((1 / (_ : ℝ) ^ 2) - 1)]
def evalOneSubOneDivSq : PositivityExt where eval {_ _α} zα pα e := do
  let (.app (.app _sub (.app (.app _div _one) (.app (.app _pow (x : Q(ℝ))) _two))) _one') ←
    withReducible (whnf e) | throwError "not ((1 / x ^ 2) - 1)"
  -- 0 < x ?
  let h1 :=
    match ← core zα pα x with
    | .positive pa => some pa
    | _ => none
  -- 0 ≤ 1 - x ?
  let h2 :=
    match ← core zα pα (q((1 : ℝ) - $x) : Q(ℝ)) with
    | .nonnegative pa => some pa
    | _ => none
  -- If 0 < x and 0 ≤ 1 - x, then 0 ≤ (1 / x ^ 2) - 1
  match h1, h2 with
  | some h1', some h2' =>
      let pa' ← mkAppM ``Real.one_sub_one_div_sq_nonneg_of_one_le #[h1', h2']
      pure (.nonnegative pa')
  | _, _ =>
      pure .none

end Mathlib.Meta.Positivity

namespace DQCP

noncomputable section

open CvxLean Minimization Real

/- TODO: where does this example come from?  -/
section QCP1

def qcp1 :=
  optimization (x y : ℝ)
    minimize (-y)
    subject to
      h1 : 1 ≤ x
      h2 : x ≤ 2
      h3 : 0 ≤ y
      h4 : sqrt ((2 * y) / (x + y)) ≤ 1

time_cmd reduction redqcp1/dcp1 : qcp1 := by
  convexify

#print dcp1
-- def dcp1 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ)
--   minimize y
--   subject to
--     h1 : 1 ≤ x
--     h2 : x ≤ 2
--     h3 : 0 ≤ y
--     h4 : y * 2 - x ≤ y

solve dcp1

#eval dcp1.value -- -2.000000

end QCP1

example : ∀ (x : ℝ),
    0 < x ∧ x ≤ 1 ∧ 1 * (1 / x) - 0 * sqrt (1 - x ^ 2) ≤ 0 →
      ((OfScientific.ofScientific 1 true 0 / x ^ OfScientific.ofScientific 2 true 0 -
              OfScientific.ofScientific 1 true 0) ^
            OfScientific.ofScientific 5 true 1) ^
          OfScientific.ofScientific 2 true 0 =
        OfScientific.ofScientific 1 true 0 / x ^ OfScientific.ofScientific 2 true 0 - OfScientific.ofScientific 1 true 0 := by {
          intros  ;
          try  {  norm_num_clean_up  ; simp_or_rw [Real.pow_half_two (by positivity_ext)] <;>  norm_num  }  <;>
          try  { simp_or_rw [Real.pow_half_two (by positivity_ext)] <;>  norm_num  }  <;>
          try  {  norm_num  }
        }

/- -/
section QCP2

def hypersonicShapeDesign (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize sqrt (1 / (Δx ^ 2) - 1)
    subject to
      h1 : 0 < Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

time_cmd reduction redqcp2/dcp2 : hypersonicShapeDesign 1 1 := by
  unfold hypersonicShapeDesign
  convexify -- FAILS

end QCP2

end

end DQCP
