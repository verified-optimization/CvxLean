import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sq

namespace CvxLean

open Real

declare_atom xexp [convex] (x : ℝ)? : x * exp x :=
vconditions (cond : 0 ≤ x)
implementationVars (t₀ : ℝ) (t₁ : ℝ)
implementationObjective t₀
implementationConstraints
  (c1 : expCone t₁ x t₀)
  (c2 : x ^ (2 : ℝ) ≤ t₁)
  (c3 : 0 ≤ x)
solution (t₀ := x * exp x) (t₁ := x ^ (2 : ℝ))
solutionEqualsAtom rfl
feasibility
  (c1 : by
    unfold expCone
    by_cases h : 0 < x
    . left
      refine ⟨h, ?_⟩
      rw [rpow_two, pow_two, ←mul_div, div_self (ne_of_lt h).symm, mul_one]
    . right
      replace h := le_of_not_lt h
      have hxeq0 := le_antisymm h cond
      simp [hxeq0])
  (c2 : by norm_num)
  (c3 : by simp [posOrthCone, cond])
optimality by {
    unfold expCone at c1
    simp at c2
    cases c1 with
    | inl c1l =>
        rcases c1l with ⟨hxpos, hxexp⟩
        apply le_trans _ hxexp
        apply mul_le_mul_of_nonneg_left _ c3
        rw [Real.exp_le_exp, le_div_iff hxpos]
        rw [pow_two] at c2
        exact c2
    | inr c1r =>
        rcases c1r with ⟨hxeq0, h0t, _⟩
        rw [hxeq0]
        simp [h0t]
  }
vconditionElimination
  (cond : c3)

end CvxLean
