import Mathbin.Data.Complex.Exponential

namespace Real

def expCone (x y z : Real) : Prop :=
  (0 < y ∧ y * exp (x / y) ≤ z) ∨ (y = 0 ∧ 0 ≤ z ∧ x ≤ 0)

def Vec.expCone (x y z : Fin n → Real) : Prop :=
  ∀ i, Real.expCone (x i) (y i) (z i)

theorem exp_iff_expCone (t x : Real) : exp x ≤ t ↔ expCone x 1 t := by
  unfold expCone
  rw [iff_def]
  apply And.intro
  · intro hexp
    apply Or.intro_left
    apply And.intro
    apply zero_lt_one
    change 1 * exp (x / 1) ≤ t
    rw [div_one, one_mul]
    assumption
  · intro h
    cases h with
    | inl h =>
      have h : 1 * exp (x / 1) ≤ t := h.2
      rwa [div_one, one_mul] at h
    | inr h =>
      sorry

end Real
