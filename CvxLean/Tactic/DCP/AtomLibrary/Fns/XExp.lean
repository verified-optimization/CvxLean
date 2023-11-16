declare_atom xexp [convex] (x : ℝ)? : x * exp x :=
vconditions (cond : 0 ≤ x)
implementationVars (t₀ : ℝ) (t₁ : ℝ) (t₂ : ℝ)
implementationObjective t₀
implementationConstraints
  (c1 : expCone t₁ x t₀)
  --(c2 : rotatedSoCone t₂ (1 / 2) ![x])
  (c2 : x ^ 2 ≤ t₂)
  (c3 : posOrthCone (t₁ - t₂))
  (c4 : posOrthCone x)
solution (t₀ := x * exp x) (t₁ := x ^ 2) (t₂ := x ^ 2)
solutionEqualsAtom rfl
feasibility
  (c1 : by {
    simp only [expCone]
    by_cases (0 < x)
    { left
      refine ⟨h, ?_⟩
      rw [rpow_two, pow_two, ←mul_div, div_self (ne_of_lt h).symm, mul_one] }
    { right
      replace h := le_of_not_lt h
      have hxeq0 := le_antisymm h cond
      simp [hxeq0] }
  })
  (c2 : by {
    -- simp [rotatedSoCone, pow_two_nonneg]
    norm_num
  })
  (c3 : by {
    simp [posOrthCone]
  })
  (c4 : by {
    simp [posOrthCone, cond]
  })
optimality by {
    simp [expCone] at c1
    simp [rotatedSoCone] at c2
    simp [posOrthCone] at c3 c4
    -- rcases c2 with ⟨hx2t₂, h0t₂, _⟩
    cases c1 with
    | inl c1l => {
        rcases c1l with ⟨hxpos, hxexp⟩
        apply le_trans _ hxexp
        apply mul_le_mul_of_nonneg_left _ c4
        rw [Real.exp_le_exp]
        rw [le_div_iff hxpos]
        rw [pow_two] at c2 --hx2t₂
        exact le_trans c2 c3--hx2t₂ c3
      }
    | inr c1r => {
        rcases c1r with ⟨hxeq0, h0t, _⟩
        rw [hxeq0]
        simp [h0t]
      }
  }
vconditionElimination
  (cond : c4)
