import CvxLean

noncomputable section

namespace OptimalVehicleSpeed

open CvxLean Minimization Real BigOperators Matrix

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
variable (F : ℝ → ℝ)
variable (F_pos : ∀ s, 0 < F s)
variable (F_increasing : ∀ s1 s2, s1 ≤ s2 → F s1 ≤ F s2)
variable (F_convex : ConvexOn ℝ ⊤ F)

open FinsetInterval

instance [i : Fact (0 < n)] : OfNat (Fin n) 0 := ⟨⟨0, i.out⟩⟩

def optimalVehicleSpeed [i : Fact (0 < n)] :=
  optimization (s : Fin n → ℝ)
    minimize ∑ i, (d i / s i) * F (s i)
    subject to
      c_smin : ∀ i, smin i ≤ s i
      c_smax : ∀ i, s i ≤ smax i
      c_τmin : ∀ i, τmin i ≤ ∑ j in [[0, i]], d j / s j
      c_τmax : ∀ i, ∑ j in [[0, i]], d j / s j ≤ τmax i

private lemma simp_vec_fraction (s : Fin n → ℝ) (i : Fin n) : d i / (d i / s i) = s i := by
  have h : d i ≠ 0 := by linarith [d_pos i]
  rw [← div_mul, div_self h, one_mul]

private lemma fold_partial_sum [Fact (0 < n)] (t : Fin n → ℝ) (i : Fin n) :
    ∑ j in [[0, i]], t j = ((const 1).toUpperTri)ᵀ.mulVec t i := by
  simp [toUpperTri, const, mulVec, Matrix.dotProduct, Finset.sum]
  apply Finset.sum_subset_zero_on_sdiff
  . simp
  . intros j hj; simp at hj
    split_ifs with h
    . have hj_nonneg : 0 ≤ j := by show 0 ≤ j.val; exact Nat.zero_le _
      replace hj := hj (.inl hj_nonneg)
      simp [not_or] at hj
      have h_contra := lt_of_lt_of_le hj.2 h
      exfalso; exact lt_irrefl _ h_contra
    . rfl
  . intros j hj
    have hi_nonneg : 0 ≤ i := by show 0 ≤ i.val; exact Nat.zero_le _
    rw [Finset.mem_uIcc, sup_of_le_right hi_nonneg] at hj
    rw [if_pos hj.2]

equivalence eqv/optimalVehicleSpeedConvex {n : ℕ} (n_pos : 0 < n) (d : Fin n → ℝ)
    (d_pos : ∀ i, 0 < d i) (τmin τmax : Fin n → ℝ) (smin smax : Fin n → ℝ)
    (smin_pos : ∀ i, 0 < smin i) (F : ℝ → ℝ) :
    optimalVehicleSpeed d τmin τmax smin smax F (i := ⟨n_pos⟩) := by
  haveI : Fact (0 < n) := ⟨n_pos⟩
  -- Change variables `s ↦ d / t`.
  -- TODO: This can be done by change of variables by detecting that the variable is a vector.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence (fun t => d / t)
    . rintro s ⟨c_smin, _⟩ i; split_ands <;> linarith [smin_pos i, c_smin i, d_pos i]
  rename_vars [t]
  -- Clean up divisions introduced by the change of variables.
  conv_obj =>
    simp only [Pi.div_apply, simp_vec_fraction d d_pos]
  conv_constr c_τmin =>
    simp only [Pi.div_apply, simp_vec_fraction d d_pos]
  conv_constr c_τmax =>
    simp only [Pi.div_apply, simp_vec_fraction d d_pos]
  -- Put in matrix form.
  equivalence_step =>
    apply Equivalence.rewrite_objFun (g := fun t => Vec.sum (t * (Vec.map F (d / t))))
    . intro t _; simp [Vec.sum]; rfl
  equivalence_step =>
    apply Equivalence.rewrite_constraint_1 (c1' := fun t => smin ≤ d / t)
    . intro t _; rfl
  equivalence_step =>
    apply Equivalence.rewrite_constraint_2 (c2' := fun t => d / t ≤ smax)
    . intro t _ _; rfl
  equivalence_step =>
    apply Equivalence.rewrite_constraint_3
      (c3' := fun t => τmin ≤ ((const 1).toUpperTri)ᵀ.mulVec t)
    . intro t _ _ _
      simp [fold_partial_sum t]; rfl
  equivalence_step =>
    apply Equivalence.rewrite_constraint_4_last
      (c4' := fun t => ((const 1).toUpperTri )ᵀ.mulVec t ≤ τmax)
    . intro t _ _ _
      simp [fold_partial_sum t]; rfl
  rename_vars [t]

#print optimalVehicleSpeedConvex

-- The problem is technically in DCP form. The only issue is that we do not have an atom for the
-- perspective function, so the objective function `Vec.sum (t * Vec.map F (d / t))` cannot be
-- reduced directly.

-- We fix `F` and declare an atom for this particular application of the perspective function.
-- Let `F(s) = a * s^2 + b * s + c` with `0 ≤ a`.

set_option trace.Meta.debug true in
declare_atom perspectiveF [convex] (n : ℕ)& (a : ℝ)& (b : ℝ)& (c : ℝ)& (d : Fin n → ℝ)?
    (t : Fin n → ℝ)? : Vec.sum (t * Vec.map (fun s => a * s ^ (2 : ℝ) + b * s + c) (d / t)) :=
bconditions
  (ha : 0 ≤ a)
  (hc : 0 ≤ c)
vconditions
  (ht : 1 / 1000 ≤ t)
implementationVars (v : Fin n → ℝ)
implementationObjective Vec.sum v
implementationConstraints
  (h : a • (d ^ (2 : ℝ) / t) + b • d + c • (1 / t) ≤ v)
solution (v := (t * Vec.map (fun s => a * s ^ (2 : ℝ) + b * s + c) (d / t)))
solutionEqualsAtom by
  rfl;
feasibility
  (h : by sorry)
optimality by
  sorry
vconditionElimination
  (ht : sorry)


end OptimalVehicleSpeed

end
