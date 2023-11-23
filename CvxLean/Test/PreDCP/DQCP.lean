import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Test.Util.TimeCmd

-- TODO: Move.
lemma Real.one_sub_one_div_sq_nonneg_of_le_one {x : ℝ} :
  0 < x → 0 ≤ 1 - x → 0 ≤ (1 / x ^ 2) - 1 :=
  fun h1 h2 => by
    have hx1 : x ≤ 1 := by linarith
    have h0x : 0 ≤ x := by positivity
    have h0x2 : 0 < x ^ 2 := by positivity
    rw [le_sub_iff_add_le, zero_add, le_div_iff h0x2, one_mul]
    simpa [abs_eq_self.mpr h0x]

lemma Real.one_sub_sq_nonneg_of_le_one {x : ℝ} :
  0 ≤ x → 0 ≤ 1 - x → 0 ≤ 1 - x ^ (2 : ℝ) :=
  fun h1 h2 => by
    have hx1 : x ≤ 1 := by linarith
    rw [le_sub_iff_add_le, zero_add]
    simpa [abs_eq_self.mpr h1]

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

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

time_cmd reduction redqcp1/dqcp1 : qcp1 := by
  convexify

#print dqcp1
-- def dqcp1 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ)
--   minimize y
--   subject to
--     h1 : 1 ≤ x
--     h2 : x ≤ 2
--     h3 : 0 ≤ y
--     h4 : y * 2 - x ≤ y

solve dqcp1

#eval dqcp1.value -- -2.000000

end QCP1

/- -/
section QCP2

def hypersonicShapeDesign (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize sqrt (1 / (Δx ^ 2) - 1)
    subject to
      h1 : 0 < Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

time_cmd reduction redqcp2/dqcp2 : hypersonicShapeDesign 0.35 0.65 := by
  unfold hypersonicShapeDesign;
  convexify
  dcp --TODO: This has 0 ≤ Δx ?????

-- solve dqcp2

end QCP2

end

end DQCP
