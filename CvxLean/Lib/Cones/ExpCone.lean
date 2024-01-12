import Mathlib.Data.Complex.Exponential

/-!
We follow the MOSEK modeling cookbook:
https://docs.mosek.com/modeling-cookbook/expo.html
-/

namespace Real

/-- The exponential cone:
      `𝒦ₑ := S₁ ∪ S₂ ⊆ ℝ³`, where
        `S₁ := { (x, y, z) | 0 < y ∧ exp(x / y) ≤ z }`, and
        `S₂ := { (x, 0, z) | 0 ≤ z ∧ x ≤ 0 }`. -/
def expCone (x y z : ℝ) : Prop :=
  (0 < y ∧ y * exp (x / y) ≤ z) ∨ (y = 0 ∧ 0 ≤ z ∧ x ≤ 0)

/-- The `n`-dimensional exponential cone `𝒦ₑⁿ`. -/
def Vec.expCone {n} [Fintype n] (x y z : n → ℝ) : Prop :=
  ∀ i, Real.expCone (x i) (y i) (z i)

/-- We have `exp(x) ≤ t ↔ (x, 1, t) ∈ 𝒦ₑ`. -/
theorem exp_iff_expCone (t x : ℝ) : exp x ≤ t ↔ expCone x 1 t := by
  unfold expCone
  rw [iff_def]
  split_ands
  { intro hexp
    apply Or.intro_left
    split_ands
    { apply Real.zero_lt_one }
    { rwa [div_one, one_mul] } }
  { intro h
    cases h with
    | inl h =>
        have h : 1 * exp (x / 1) ≤ t := h.2
        rwa [div_one, one_mul] at h
    | inr h =>
        exfalso
        exact zero_ne_one h.1.symm }

end Real
