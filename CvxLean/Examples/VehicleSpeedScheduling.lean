import CvxLean

noncomputable section

namespace VehicleSpeedSched

open CvxLean Minimization Real BigOperators Matrix

-- Number of segments.
variable (n : ℕ)

-- Travel distance of segment i.
variable (d : Fin n → ℝ)

-- Arrival to segment i time bounds.
variable (τmin τmax : Fin n → ℝ)

-- Minimum and maximum speed at segment i.
variable (smin smax : Fin n → ℝ)

-- Fuel use function (input is speed).
variable (F : ℝ → ℝ)

open FinsetInterval

def vehSpeedSched [Fact (0 < n)] :=
  optimization (s : Fin n → ℝ)
    minimize ∑ i, (d i / s i) * F (s i)
    subject to
      c_smin : ∀ i, smin i ≤ s i
      c_smax : ∀ i, s i ≤ smax i
      c_τmin : ∀ i, τmin i ≤ ∑ j in [[0, i]], d j / s j
      c_τmax : ∀ i, ∑ j in [[0, i]], d j / s j ≤ τmax i

variable {n}

private lemma simp_vec_fraction (h_d_pos : StrongLT 0 d) (s : Fin n → ℝ) (i : Fin n) :
    d i / (d i / s i) = s i := by
  have h_di_pos := h_d_pos i; simp at h_di_pos;
  have h_di_nonzero : d i ≠ 0 := by linarith
  rw [← div_mul, div_self h_di_nonzero, one_mul]

private lemma fold_partial_sum [hn : Fact (0 < n)] (t : Fin n → ℝ) (i : Fin n) :
    ∑ j in [[0, i]], t j = Vec.cumsum t i := by
  simp [Vec.cumsum]; split_ifs
  . rfl
  . linarith [hn.out]

equivalence' eqv₁/vehSpeedSchedConvex (n : ℕ) (d : Fin n → ℝ)
    (τmin τmax smin smax : Fin n → ℝ) (F : ℝ → ℝ) (h_n_pos : 0 < n) (h_d_pos : StrongLT 0 d)
    (h_smin_pos : StrongLT 0 smin) : @vehSpeedSched n d τmin τmax smin smax F ⟨h_n_pos⟩ := by
  replace h_d_pos : ∀ i, 0 < d i := fun i => h_d_pos i
  replace h_smin_pos : ∀ i, 0 < smin i := fun i => h_smin_pos i
  haveI : Fact (0 < n) := ⟨h_n_pos⟩
  -- Change variables `s ↦ d / t`.
  -- TODO: This can be done by change of variables by detecting that the variable is a vector.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence (fun t => d / t)
    . rintro s ⟨c_smin, _⟩ i; split_ands <;> linarith [h_smin_pos i, c_smin i, h_d_pos i]
  rename_vars [t]
  -- Clean up divisions introduced by the change of variables.
  conv_obj => simp only [Pi.div_apply, simp_vec_fraction d h_d_pos]
  conv_constr c_τmin => simp only [Pi.div_apply, simp_vec_fraction d h_d_pos]
  conv_constr c_τmax => simp only [Pi.div_apply, simp_vec_fraction d h_d_pos]
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
    apply Equivalence.rewrite_constraint_3 (c3' := fun t => τmin ≤ Vec.cumsum t)
    . intro t _ _ _; simp [fold_partial_sum t]; rfl
  equivalence_step =>
    apply Equivalence.rewrite_constraint_4_last (c4' := fun t => Vec.cumsum t ≤ τmax)
    . intro t _ _ _; simp [fold_partial_sum t]; rfl
  rename_vars [t]
  rename_constrs [c_smin, c_smax, c_τmin, c_τmax]

#print vehSpeedSchedConvex

#check eqv₁.backward_map

-- The problem is technically in DCP form if `F` is DCP convex. The only issue is that we do not
-- have an atom for the perspective function, so the objective function
-- `Vec.sum (t * Vec.map F (d / t))` cannot be reduced directly.

-- However, if we fix `F`, we can use other atoms. For example, if `F` is quadratic, the problem can
-- be reduced. Let `F(s) = a * s^2 + b * s + c` with `0 ≤ a`.

equivalence' eqv₂/vehSpeedSchedQuadratic (n : ℕ) (d : Fin n → ℝ)
    (τmin τmax smin smax : Fin n → ℝ) (a b c : ℝ) (h_n_pos : 0 < n) (h_d_pos : StrongLT 0 d)
    (h_smin_pos : StrongLT 0 smin) :
    vehSpeedSchedConvex n d τmin τmax smin smax (fun s => a • s ^ (2 : ℝ) + b • s + c)
      h_n_pos h_d_pos h_smin_pos := by
  have t_pos_of_c_smin : ∀ t, smin ≤ d / t → StrongLT 0 t := fun t h i => by
    have h_di_div_ti_pos := lt_of_lt_of_le (h_smin_pos i) (h i)
    cases div_pos_iff.mp h_di_div_ti_pos with
    | inl h_pos => exact h_pos.2
    | inr h_neg => have d_pos_i := h_d_pos i; simp at d_pos_i ⊢; linarith [h_neg.1, d_pos_i]
  -- Add constraint to tell the system that `t` is `ε`-nonnegative.
  equivalence_step =>
    apply Equivalence.add_constraint (cs' := fun t => StrongLT 0 t)
    . rintro t ⟨c_smin, _⟩ i
      exact t_pos_of_c_smin t c_smin i
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  -- Arithmetic simplification in the objective function.
  equivalence_step =>
    apply Equivalence.rewrite_objFun
      (g := fun t => Vec.sum (a • (d ^ (2 : ℝ)) * (1 / t) + b • d + c • t))
    . rintro t ⟨c_t, _⟩
      congr; funext i; unfold Vec.map; dsimp
      have h_ti_pos : 0 < t i := c_t i
      field_simp; ring
  -- Rewrite linear constraints.
  equivalence_step =>
    apply Equivalence.rewrite_constraint_2 (c2' := fun t => smin * t ≤ d)
    . intro t c_t _; rw [Vec.le_div_iff c_t]
  rename_vars [t]
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  equivalence_step =>
    apply Equivalence.rewrite_constraint_3 (c3' := fun t => d ≤ smax * t)
    . intro t c_t _ _; rw [Vec.div_le_iff c_t]
  rename_vars [t]
  rename_constrs [c_t, c_smin, c_smax, c_τmin, c_τmax]
  -- Finally, we can apply `dcp`! (or we can call `solve`, as we do below).

#print vehSpeedSchedQuadratic

#check eqv₂.backward_map

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

lemma dₚ_pos : StrongLT 0 dₚ := by
  intro i; fin_cases i <;> (simp [dₚ]; norm_num)

@[optimization_param]
def τminₚ : Fin nₚ → ℝ :=
  ![1.0809, 2.7265, 3.5118, 5.3038, 5.4516, 7.1648, 9.2674, 12.1543, 14.4058, 16.6258]

@[optimization_param]
def τmaxₚ : Fin nₚ → ℝ :=
  ![4.6528, 6.5147, 7.5178, 9.7478, 9.0641, 10.3891, 13.1540, 16.0878, 17.4352, 20.9539]

@[optimization_param]
def sminₚ : Fin nₚ → ℝ :=
  ![0.7828, 0.6235, 0.7155, 0.5340, 0.6329, 0.4259, 0.7798, 0.9604, 0.7298, 0.8405]

@[optimization_param]
def smaxₚ : Fin nₚ → ℝ :=
  ![1.9624, 1.6036, 1.6439, 1.5641, 1.7194, 1.9090, 1.3193, 1.3366, 1.9470, 2.8803]

lemma sminₚ_pos : StrongLT 0 sminₚ := by
  intro i; fin_cases i <;> (simp [sminₚ]; norm_num)

@[simp]
lemma sminₚ_nonneg : 0 ≤ sminₚ := le_of_strongLT sminₚ_pos

lemma sminₚ_le_smaxₚ : sminₚ ≤ smaxₚ := by
  intro i; fin_cases i <;> (simp [sminₚ, smaxₚ]; norm_num)

@[simp]
lemma smaxₚ_nonneg : 0 ≤ smaxₚ := le_trans sminₚ_nonneg sminₚ_le_smaxₚ

@[optimization_param]
def aₚ : ℝ := 1

@[simp]
lemma aₚ_nonneg : 0 ≤ aₚ := by unfold aₚ; norm_num

@[simp]
lemma aₚdₚ2_nonneg : 0 ≤ aₚ • (dₚ ^ (2 : ℝ)) := by
  intros i; fin_cases i <;> (simp [aₚ, dₚ]; norm_num)

@[optimization_param]
def bₚ : ℝ := 6

@[optimization_param]
def cₚ : ℝ := 10

def p := vehSpeedSchedQuadratic nₚ dₚ τminₚ τmaxₚ sminₚ smaxₚ aₚ bₚ cₚ nₚ_pos dₚ_pos sminₚ_pos

set_option trace.Meta.debug true

solve p

#eval p.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval p.value    -- 275.042133
#eval p.solution -- ...

-- NOTE: F is not really used here, but it is a parameter of the equivalence, so we must give it a
-- value.
def eqv₁.backward_mapₚ := eqv₁.backward_map nₚ dₚ.float τminₚ.float τmaxₚ.float sminₚ.float
  smaxₚ.float (fun s => aₚ.float * s ^ 2 + bₚ.float * s + cₚ.float)

def eqv₂.backward_mapₚ := eqv₂.backward_map nₚ dₚ.float τminₚ.float τmaxₚ.float sminₚ.float
  smaxₚ.float aₚ.float bₚ.float cₚ.float

-- Finally, we can obtain the solution to the original problem.

def sol := eqv₁.backward_mapₚ (eqv₂.backward_mapₚ p.solution)

#eval sol
-- ![0.955578, 0.955548, 0.955565, 0.955532, 0.955564, 0.955560, 0.912362, 0.960401, 0.912365,
--   0.912375]

end VehicleSpeedSched

end
