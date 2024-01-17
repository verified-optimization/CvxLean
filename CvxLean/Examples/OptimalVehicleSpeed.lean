import CvxLean.Command.Equivalence
import CvxLean.Command.Solve
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.Basic.RenameVars

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

private lemma simp_vec_fraction : ∀ s : Fin n → ℝ, ∀ i, d i / (d i / s i) = s i := by
  intros s i
  have h : d i ≠ 0 := by
    have d_pos_i := d_pos i
    linarith
  rw [← div_mul, div_self h, one_mul]

equivalence eqv/optimalVehicleSpeedConvex {n : ℕ} (n_pos : 0 < n) (d : Fin n → ℝ)
    (d_pos : ∀ i, 0 < d i) (τmin τmax : Fin n → ℝ) (smin smax : Fin n → ℝ)
    (smin_pos : ∀ i, 0 < smin i) (Φ : ℝ → ℝ) :
    optimalVehicleSpeed d τmin τmax smin smax Φ ⟨n_pos⟩ := by
  equivalence_step =>
    -- IDEA: This can be done by change of variables by detecting that the
    -- variable is a vector.
    apply ChangeOfVariables.toEquivalence (fun t => d / t)
    . rintro s ⟨hsmin, _hsmax, _hτmin, _hτmax⟩ i
      split_ands
      . have smin_pos_i := smin_pos i
        have hsmin_i := hsmin i
        linarith
      . have d_pos_i := d_pos i
        linarith
  rename_vars [t]
  conv_obj =>
    simp only [Pi.div_apply, simp_vec_fraction d d_pos]
  conv_constr hτmin =>
    simp only [Pi.div_apply, simp_vec_fraction d d_pos]
  conv_constr hτmax =>
    simp only [Pi.div_apply, simp_vec_fraction d d_pos]

#print optimalVehicleSpeedConvex

end OptimalVehicleSpeed
