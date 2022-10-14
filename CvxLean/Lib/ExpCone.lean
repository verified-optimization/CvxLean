import Mathbin.Data.Set.Basic
import Mathbin.Data.Complex.Exponential
import CvxLean.Lib.Missing.Mathlib
import Mathbin.Algebra.GroupWithZero.Basic

attribute [-simp] Set.inj_on_empty Set.inj_on_singleton Quot.lift_on₂_mk Quot.lift_on_mk Quot.lift₂_mk

namespace Real

def expCone (x y z : ℝ) : Prop :=
  (0 < y ∧ y * exp (x / y) ≤ z) ∨ (y = 0 ∧ 0 ≤ z ∧ x ≤ 0)

def Vec.expCone (x y z : Finₓ n → ℝ) : Prop :=
  ∀ i, Real.expCone (x i) (y i) (z i)

theorem exp_iff_expCone (t x : ℝ) : exp x ≤ t ↔ expCone x 1 t := by
  unfold expCone
  rw [iff_def]
  apply And.intro
  · intro hexp
    apply Or.intro_left
    apply And.intro
    apply zero_lt_one
    change One.one * exp (x / One.one) ≤ t
    rw [@div_one ℝ (@GroupWithZeroₓ.toDivisionMonoid Real
      (@DivisionSemiring.toGroupWithZero Real (@DivisionRing.toDivisionSemiring Real Real.divisionRing)))]
    rw [one_mulₓ]
    assumption
  · intro h
    cases h with
    | inl h =>
      have h : One.one * exp (x / One.one) ≤ t := h.2
      rwa [@div_one ℝ (@GroupWithZeroₓ.toDivisionMonoid Real
        (@DivisionSemiring.toGroupWithZero Real (@DivisionRing.toDivisionSemiring Real Real.divisionRing))),
        one_mulₓ] at h
    | inr h =>
      exfalso
      apply @one_ne_zero Real
      apply h.1

end Real
