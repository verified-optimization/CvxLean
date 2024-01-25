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

set_option trace.Meta.debug true

equivalence' eqv/optimalVehicleSpeedConvex {n : ℕ} (n_pos : 0 < n) {d : Fin n → ℝ}
    (d_ε_nonneg : ∀ i, 1 / 100000 ≤ d i) (τmin τmax smin smax : Fin n → ℝ)
    (smin_ε_nonneg : ∀ i, 1 / 100000 ≤ smin i) (smin_le_max : smin ≤ smax)
    (smax_le_one : ∀ i, smax i ≤ 1)  (F : ℝ → ℝ) :
    optimalVehicleSpeed d τmin τmax smin smax F (i := ⟨n_pos⟩) := by
  have d_pos : ∀ i, 0 < d i := fun i => by linarith [d_ε_nonneg i]
  have smin_pos : ∀ i, 0 < smin i := fun i => by linarith [smin_ε_nonneg i]
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

#check eqv.backward_map

-- The problem is technically in DCP form. The only issue is that we do not have an atom for the
-- perspective function, so the objective function `Vec.sum (t * Vec.map F (d / t))` cannot be
-- reduced directly.

-- We fix `F` and declare an atom for this particular application of the perspective function.
-- Let `F(s) = a * s^2 + b * s + c` with `0 ≤ a`.

equivalence' eqv'/optimalVehicleSpeedConvex' {n : ℕ} (n_pos : 0 < n) {d : Fin n → ℝ}
    (d_ε_nonneg : ∀ i, 1 / 100000 ≤ d i) (τmin τmax smin smax : Fin n → ℝ)
    (smin_ε_nonneg : ∀ i, 1 / 100000 ≤ smin i) (smin_le_max : smin ≤ smax)
    (smax_le_one : ∀ i, smax i ≤ 1) (a b c : ℝ) (ha : 0 ≤ a) :
    optimalVehicleSpeedConvex n_pos d_ε_nonneg τmin τmax smin smax smin_ε_nonneg smin_le_max
      smax_le_one (fun s => a • s ^ (2 : ℝ) + b • s + c) := by
  have d_pos : StrongLT 0 d := fun i => by simp; linarith [d_ε_nonneg i]
  have smin_pos : StrongLT 0 smin := fun i => by simp; linarith [smin_ε_nonneg i]
  have smin_nonneg := le_of_strongLT smin_pos
  have smax_nonneg := le_trans smin_nonneg smin_le_max
  have t_pos_of_c_smin : ∀ t, smin ≤ d / t → StrongLT 0 t := fun t h i => by
    have h_di_div_ti_pos := lt_of_lt_of_le (smin_pos i) (h i)
    cases div_pos_iff.mp h_di_div_ti_pos with
    | inl h_pos => exact h_pos.2
    | inr h_neg => have d_pos_i := d_pos i; simp at d_pos_i ⊢; linarith [h_neg.1, d_pos_i]
  -- Add constraint to tell the system that `t` is `ε`-nonnegative.
  equivalence_step =>
    apply Equivalence.add_constraint (cs' := fun t => 1 / 100000 ≤ t)
    . rintro t ⟨c_smin, c_smax, _, _⟩ i
      have h_ti_pos : 0 < t i := t_pos_of_c_smin t c_smin i
      have h_di_ti := le_trans (c_smax i) (smax_le_one i)
      simp at h_di_ti
      rw [div_le_iff h_ti_pos, one_mul] at h_di_ti
      exact le_trans (d_ε_nonneg i) h_di_ti
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  -- Arithmetic simplification in the objective function.
  equivalence_step =>
    apply Equivalence.rewrite_objFun (g := fun t => Vec.sum (a • (d ^ (2 : ℝ) / t) + b • d + c • t))
    . rintro t ⟨_, c_smin, _, _, _⟩
      congr; funext i; unfold Vec.map; dsimp
      have h_ti_pos : 0 < t i := t_pos_of_c_smin t c_smin i
      field_simp; ring
  rename_vars [t]
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  -- Rewrite linear constraints.
  equivalence_step =>
    apply Equivalence.rewrite_constraint_2 (c2' := fun t => smin * t ≤ d)
    . rintro t c_t _; constructor
      . intro h i; have hi := h i; simp at hi;
        have h_ti_pos : 0 < t i := lt_of_lt_of_le (by norm_num) (c_t i)
        rw [le_div_iff h_ti_pos] at hi; exact hi
      . intro h i; have hi := h i; simp at hi;
        have h_ti_pos : 0 < t i := lt_of_lt_of_le (by norm_num) (c_t i)
        dsimp; rw [le_div_iff h_ti_pos]; exact hi
  rename_vars [t]
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  equivalence_step =>
    apply Equivalence.rewrite_constraint_3 (c3' := fun t => d ≤ smax * t)
    . rintro t c_t _ _; constructor
      . intro h i; have hi := h i; simp at hi;
        have h_ti_pos : 0 < t i := lt_of_lt_of_le (by norm_num) (c_t i)
        rw [div_le_iff h_ti_pos] at hi; exact hi
      . intro h i; have hi := h i; simp at hi;
        have h_ti_pos : 0 < t i := lt_of_lt_of_le (by norm_num) (c_t i)
        dsimp; rw [div_le_iff h_ti_pos]; exact hi
  rename_vars [t]
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  -- Finally, we can apply DCP!
  dcp

#print optimalVehicleSpeedConvex'

#check eqv'.backward_map

-- Now, let's solve a concrete instance of the problem:
-- https://github.com/cvxgrp/cvxbook_additional_exercises/blob/main/python/veh_speed_sched_data.py

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

@[optimization_param]
def nₚ : ℕ := 10

lemma nₚ_pos : 0 < nₚ := by unfold nₚ; norm_num

@[optimization_param]
def dₚ : Fin nₚ → ℝ :=
  ![1.9501, 1.2311, 1.6068, 1.4860, 1.8913, 1.7621, 1.4565, 1.0185, 1.8214, 1.4447]

lemma dₚ_ε_nonneg : ∀ i, 1 / 100000 ≤ dₚ i := by
  intro i; fin_cases i <;> (simp [dₚ]; norm_num)

@[optimization_param]
def τminₚ : Fin nₚ → ℝ :=
  ![1.0809, 2.7265, 3.5118, 5.3038, 5.4516, 7.1648, 9.2674, 12.1543, 14.4058, 16.6258]

@[optimization_param]
def τmaxₚ : Fin nₚ → ℝ :=
  ![4.6528, 6.5147, 7.5178, 9.7478, 9.0641, 10.3891, 13.1540, 16.0878, 17.4352, 20.9539]

@[optimization_param]
def sminₚ : Fin nₚ → ℝ :=
  (0.2 : ℝ) • ![0.7828, 0.6235, 0.7155, 0.5340, 0.6329, 0.4259, 0.7798, 0.9604, 0.7298, 0.8405]

@[optimization_param]
def smaxₚ : Fin nₚ → ℝ :=
  (0.2 : ℝ) • ![1.9624, 1.6036, 1.6439, 1.5641, 1.7194, 1.9090, 1.3193, 1.3366, 1.9470, 2.8803]

lemma sminₚ_ε_nonneg : ∀ i, 1 / 100000 ≤ sminₚ i := by
  intro i; fin_cases i <;> (simp [sminₚ]; norm_num)

@[simp]
lemma sminₚ_nonneg : 0 ≤ sminₚ := fun i => le_trans (by norm_num) (sminₚ_ε_nonneg i)

lemma sminₚ_le_smaxₚ : sminₚ ≤ smaxₚ := by
  intro i; fin_cases i <;> (simp [sminₚ, smaxₚ]; norm_num)

@[simp]
lemma smaxₚ_nonneg : 0 ≤ smaxₚ := le_trans sminₚ_nonneg sminₚ_le_smaxₚ

lemma smaxₚ_le_one : ∀ i, smaxₚ i ≤ 1 := by
  intro i; fin_cases i <;> (simp [smaxₚ]; norm_num)

@[optimization_param]
def aₚ : ℝ := 1

lemma aₚ_nonneg : 0 ≤ aₚ := by unfold aₚ; norm_num

@[optimization_param]
def bₚ : ℝ := 6

@[optimization_param]
def cₚ : ℝ := 10

def p := optimalVehicleSpeedConvex' nₚ_pos dₚ_ε_nonneg τminₚ τmaxₚ sminₚ smaxₚ sminₚ_ε_nonneg
  sminₚ_le_smaxₚ smaxₚ_le_one aₚ bₚ cₚ aₚ_nonneg

set_option trace.Meta.debug true

solve p

#eval p.status
#eval p.value
#eval p.solution

-- def sol := eqv.backward_map (eqv'.backward_map (p.solution))

-- #eval sol

end OptimalVehicleSpeed

end
