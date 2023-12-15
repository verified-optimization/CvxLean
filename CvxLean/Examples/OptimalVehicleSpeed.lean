import CvxLean.Command.Equivalence
import CvxLean.Command.Solve
import CvxLean.Tactic.Basic.Rename
import CvxLean.Tactic.ChangeOfVariables.ChangeOfVariables

noncomputable section OptimalVehicleSpeed

open CvxLean Minimization Real BigOperators

-- Number of segments.
variable {n : ℕ}
variable (n_pos : 0 < n)

-- Travel distance of segment i.
variable (d : Fin n → ℝ)
variable (d_pos : ∀ i, 0 < d i)

-- Arrival to segment i time bounds.
variable (τmin τmax : Fin n → ℝ)
variable (τmin_pos : ∀ i, 0 < τmin i)
variable (τmin_le_τmax : ∀ i, τmin i ≤ τmax i)

-- Minimum and maximum speed at segment i.
variable (smin smax : Fin n → ℝ)
variable (smin_pos : ∀ i, 0 < smin i)
variable (smin_le_smax : ∀ i, smin i ≤ smax i)

-- Fuel use function (input is speed).
variable (Φ : ℝ → ℝ)
variable (Φ_pos : ∀ s, 0 < Φ s)
variable (Φ_increasing : ∀ s1 s2, s1 ≤ s2 → Φ s1 ≤ Φ s2)
variable (Φ_convex : ConvexOn ℝ ⊤ Φ)

open FinsetInterval

instance [i : Fact (0 < n)] : OfNat (Fin n) 0 := ⟨⟨0, i.out⟩⟩

def optimalVehicleSpeed (_ : Fact (0 < n)) :=
  optimization (s : Fin n → ℝ)
    minimize ∑ i, (d i / s i) * Φ (s i)
    subject to
      hsmin : ∀ i, smin i ≤ s i
      hsmax : ∀ i, s i ≤ smax i
      hτmin : ∀ i, τmin i ≤ ∑ j in [[0, i]], d j / s j
      hτmax : ∀ i, ∑ j in [[0, i]], d j / s j ≤ τmax i

private lemma simp_fraction : ∀ s : Fin n → ℝ, ∀ i, d i / (d i / s i) = s i := by {
  intros s i
  have h : d i ≠ 0 := by {
    have d_pos_i := d_pos i
    linarith
  }
  rw [← div_mul, div_self h, one_mul]
}

equivalence equiv/optimalVehicleSpeedConvex
  {n : ℕ}
  (n_pos : 0 < n)
  (d : Fin n → ℝ)
  (d_pos : ∀ i, 0 < d i)
  (τmin τmax : Fin n → ℝ)
  (smin smax : Fin n → ℝ)
  (smin_pos : ∀ i, 0 < smin i)
  (Φ : ℝ → ℝ) :
  optimalVehicleSpeed d τmin τmax smin smax Φ ⟨n_pos⟩ := by
  unfold optimalVehicleSpeed
  apply Minimization.Equivalence.trans
  apply ChangeOfVariables.toEquivalence (fun t => d / t)
  { rintro s ⟨hsmin, _hsmax, _hτmin, _hτmax⟩ i
    split_ands
    { --suffices h : 0 < s i by exact (ne_of_lt h).symm
      --exact lt_of_lt_of_le (smin_pos i) (hsmin i)
      have smin_pos_i := smin_pos i
      have hsmin_i := hsmin i
      linarith
      }
    { --exact (ne_of_lt (d_pos i)).symm
      have d_pos_i := d_pos i
      linarith
      } }
  -- IDEA: This can be done by change of variables by detecting that the
  -- variable is a vector.
  apply Minimization.Equivalence.trans
  apply MinimizationQ.rewrite_objective
  { rintro s ⟨_hsmin, _hsmax, _hτmin, _hτmax⟩
    simp only [Pi.div_apply, simp_fraction d d_pos s]
    rfl
  }
  apply Minimization.Equivalence.trans
  apply MinimizationQ.rewrite_constraint_3
  { rintro s _hsmin _hsmax _hτmax
    simp only [Pi.div_apply, simp_fraction d d_pos s]
    rfl
  }
  apply Minimization.Equivalence.trans
  apply MinimizationQ.rewrite_constraint_4_last
  { rintro s _hsmin _hsmax _hτmax
    simp only [Pi.div_apply]
    simp only [simp_fraction d d_pos s]
    rfl
  }
  equivalence_rfl

#print optimalVehicleSpeedConvex

-- TODO: Fatal error using conv inside equivalence.

-- TODO: rename_vars in equivalence mode.

-- IDEA: simplify_objective [...], simplify_constraint i [...],
-- Also rewrite_objective and rewrite_constraint. Potentially get rid of the
-- rewrite_constraint_x lemmas and handle that in meta.

end OptimalVehicleSpeed
