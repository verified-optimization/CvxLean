import CvxLean

noncomputable section

namespace TrussDesign

open CvxLean Minimization Real

-- Height range (distance between the upper bearing's `y` coordinate and the joint's `y` coordinate;
-- which is the same as the distance from the lower bearing's `y` coordinate, as the truss is
-- assumed to be symmetric along the joint's `x` line).
variable (hmin hmax : ℝ)
variable (hmin_pos : 0 < hmin) (hmin_le_hmax : hmin ≤ hmax)

-- Width range (distance between the bearings' `x` coordinate and the joint's `x` coordinate).
variable (wmin wmax : ℝ)
variable (wmin_pos : 0 < wmin) (wmin_le_wmax : wmin ≤ wmax)

-- Maximum outer radius of the bar.
variable (Rmax : ℝ)

-- Maximum allowable stress.
variable (σ : ℝ)

-- Vertical downward force on the joint.
variable (F₁ : ℝ)

-- Horizontal left-to-right force on the joint.
variable (F₂ : ℝ)

def trussDesign :=
  optimization (h w r R : ℝ) with A := 2 * π * (R ^ 2 - r ^ 2)
    minimize 2 * A * sqrt (w ^ 2 + h ^ 2)
    subject to
      c_r    : 0 < r
      c_F₁   : F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ σ * A
      c_F₂   : F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ σ * A
      c_hmin : hmin ≤ h
      c_hmax : h ≤ hmax
      c_wmin : wmin ≤ w
      c_wmax : w ≤ wmax
      c_R_lb : 1.1 * r ≤ R
      c_R_ub : R ≤ Rmax

instance : ChangeOfVariables
    fun ((h, w, r, A) : ℝ × ℝ × ℝ × ℝ) => (h, w, r, sqrt (A / (2 * π) + r ^ 2)) :=
  { inv := fun (h, w, r, R) => (h, w, r, 2 * π * (R ^ 2 - r ^ 2)),
    condition := fun (_, _, _, R) => 0 ≤ R,
    property := fun (h, w, r, R) hR => by
      simp; rw [mul_comm _ (R ^ 2 - r ^ 2), ← mul_div, div_self (by positivity), mul_one]
      ring_nf; exact sqrt_sq hR }

instance : ChangeOfVariables
    fun ((h', w', r', A') : ℝ × ℝ × ℝ × ℝ) => (exp h', exp w', exp r', exp A') :=
  { inv := fun (h, w, r, A) => (log h, log w, log r, log A),
    condition := fun (h', w', r', A') => 0 < h' ∧ 0 < w' ∧ 0 < r' ∧ 0 < A',
    property := fun (h', w', r', A') ⟨hh', hw', hr', hA'⟩ => by
      simp [exp_log hh', exp_log hw', exp_log hr', exp_log hA'] }

equivalence eqv/trussDesignConvex (hmin hmax : ℝ) (hmin_pos : 0 < hmin) (hmin_le_hmax : hmin ≤ hmax)
    (wmin wmax : ℝ) (wmin_pos : 0 < wmin) (wmin_le_wmax : wmin ≤ wmax) (Rmax : ℝ)
    (Rmax_nonneg : 0 < Rmax) (σ : ℝ) (σ_nonneg : 0 < σ) (F₁ : ℝ) (F₁_nonneg : 0 < F₁) (F₂ : ℝ)
    (F₂_nonneg : 0 < F₂) : trussDesign hmin hmax wmin wmax Rmax σ F₁ F₂ := by
  -- Apply key change of variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        (hwrA.1, hwrA.2.1, hwrA.2.2.1, sqrt (hwrA.2.2.2 / (2 * π) + hwrA.2.2.1 ^ 2)))
    . rintro ⟨h, w, r, R⟩ ⟨c_r, _, _, _, _, _, _, c_R_lb, _⟩; dsimp at *
      simp [ChangeOfVariables.condition]
      have h_r_le : r ≤ 1.1 * r := (le_mul_iff_one_le_left c_r).mpr (by norm_num)
      exact le_trans (le_of_lt c_r) (le_trans h_r_le c_R_lb)
  rename_vars [h, w, r, A]; dsimp
  -- Rewrite contraint `c_R_lb`.
  equivalence_step =>
    apply Equivalence.rewrite_constraint_8
      (c8' := fun (hwrA : ℝ × ℝ × ℝ × ℝ) => 0.21 * hwrA.2.2.1 ^ 2 ≤ hwrA.2.2.2 / (2 * π))
    . rintro ⟨h, w, r, A⟩ c_r _ _ _ _ _ _ _; dsimp at *
      rw [le_sqrt' (by positivity), rpow_two, mul_pow, ← sub_le_iff_le_add]
      rw [iff_eq_eq]; congr; ring_nf
  have h_A_div_2π_add_r2_nonneg : ∀ (r A : ℝ) (c_r : 0 < r)
    (c_R_lb : 0.21 * r ^ 2 ≤ A / (2 * π)), 0 ≤ A / (2 * π) + r ^ 2 :=
    fun r A c_r c_R_lb => by
      have h_A_div_2π_nonneg : 0 ≤ A / (2 * π) := le_trans (by positivity) c_R_lb
      exact add_nonneg (h_A_div_2π_nonneg) (by positivity)
  -- Simplify objective function.
  equivalence_step =>
    apply Equivalence.rewrite_objFun
      (g := fun (hwrA : ℝ × ℝ × ℝ × ℝ) => 2 * hwrA.2.2.2 * sqrt (hwrA.2.1 ^ 2 + hwrA.1 ^ 2))
    . rintro ⟨h, w, r, A⟩ ⟨c_r, _, _, _, _, _, _, c_R_lb, _⟩; dsimp at *
      rw [rpow_two, sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
      ring_nf; field_simp; ring
  rename_vars [h, w, r, A]
  -- Simplify constraint `c_F₁`.
  equivalence_step =>
    apply Equivalence.rewrite_constraint_2
      (c2' := fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        F₁ * sqrt (hwrA.2.1 ^ 2 + hwrA.1 ^ 2) / (2 * hwrA.1) ≤ σ * hwrA.2.2.2)
    . rintro ⟨h, w, r, A⟩ c_r ⟨_, _, _, _, _, c_R_lb, _⟩; dsimp at *
      rw [rpow_two (sqrt (_ + r ^ 2)), sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
      rw [iff_eq_eq]; congr; ring_nf; field_simp; ring
  rename_vars [h, w, r, A]
  -- Simplify constraint `c_F₂`.
  equivalence_step =>
    apply Equivalence.rewrite_constraint_3
      (c3' := fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        F₂ * sqrt (hwrA.2.1 ^ 2 + hwrA.1 ^ 2) / (2 * hwrA.2.1) ≤ σ * hwrA.2.2.2)
    . rintro ⟨h, w, r, A⟩ c_r _ ⟨_, _, _, _, c_R_lb, _⟩; dsimp at *
      rw [rpow_two (sqrt (_ + r ^ 2)), sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
      rw [iff_eq_eq]; congr; ring_nf; field_simp; ring
  rename_vars [h, w, r, A]
  rename_constrs [c_r, c_F₁, c_F₂, c_hmin, c_hmax, c_wmin, c_wmax, c_A_lb, c_A_ub]
  -- Change variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        (exp hwrA.1, exp hwrA.2.1, exp hwrA.2.2.1, exp hwrA.2.2.2))
    . rintro ⟨h, w, r, A⟩ ⟨c_r, _, _, c_hmin, _, c_wmin, _, c_A_lb, _⟩; dsimp at *
      split_ands
      . exact lt_of_lt_of_le hmin_pos c_hmin
      . exact lt_of_lt_of_le wmin_pos c_wmin
      . exact c_r
      . have h_A_div_2π_pos : 0 < A / (2 * π) := lt_of_lt_of_le (by positivity) c_A_lb
        rwa [lt_div_iff (by positivity), zero_mul] at h_A_div_2π_pos
  dsimp
  rename_vars [h', w', r', A']
  remove_trivial_constrs
  -- Apply pre-DCP.
  pre_dcp

#print trussDesignConvex


-- hmin = wmin = 1, hmax = wmax = 100, Rmax = 10, σ = 0.5.
-- F1 = 10 F2 = 20

end TrussDesign

end
