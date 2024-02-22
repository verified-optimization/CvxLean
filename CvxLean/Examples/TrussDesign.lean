import CvxLean

/-!
# Case study: Truss design

See section 6.3 in https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf.
-/

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

equivalence' eqv₁/trussDesignGP (hmin hmax wmin wmax Rmax σ F₁ F₂ : ℝ) :
    trussDesign hmin hmax wmin wmax Rmax σ F₁ F₂ := by
  -- Apply key change of variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (hwrA : ℝ × ℝ × ℝ × ℝ) =>
        (hwrA.1, hwrA.2.1, hwrA.2.2.1, sqrt (hwrA.2.2.2 / (2 * π) + hwrA.2.2.1 ^ 2)))
    . rintro ⟨h, w, r, R⟩ ⟨c_r, _, _, _, _, _, _, c_R_lb, _⟩; dsimp at *
      simp [ChangeOfVariables.condition]
      have h_r_le : r ≤ 1.1 * r := (le_mul_iff_one_le_left c_r).mpr (by norm_num)
      exact le_trans (le_of_lt c_r) (le_trans h_r_le c_R_lb)
  rename_vars [h, w, r, A]
  -- Some cleanup.
  conv_opt => dsimp
  -- Rewrite contraint `c_R_lb`.
  rw_constr c_R_lb into (0.21 * r ^ 2 ≤ A / (2 * π)) =>
    rw [le_sqrt' (by positivity), rpow_two, mul_pow, ← sub_le_iff_le_add]
    rw [iff_eq_eq]; congr; ring_nf
  -- Useful fact about constraints used for simplification. This is a good example of introducing
  -- local lemmas in an `equivalence` environment.
  have h_A_div_2π_add_r2_nonneg : ∀ (r A : ℝ) (c_r : 0 < r)
    (c_R_lb : 0.21 * r ^ 2 ≤ A / (2 * π)), 0 ≤ A / (2 * π) + r ^ 2 :=
    fun r A c_r c_R_lb => by
      have h_A_div_2π_nonneg : 0 ≤ A / (2 * π) := le_trans (by positivity) c_R_lb
      exact add_nonneg (h_A_div_2π_nonneg) (by positivity)
  -- Simplify objective function.
  rw_obj into (2 * A * sqrt (w ^ 2 + h ^ 2)) =>
    rw [rpow_two, sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
    ring_nf; field_simp; ring
  -- Simplify constraint `c_F₁`.
  rw_constr c_F₁ into (F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ σ * A) =>
    rw [rpow_two (sqrt (_ + r ^ 2)), sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
    rw [iff_eq_eq]; congr; ring_nf; field_simp; ring
  -- Simplify constraint `c_F₂`.
  rw_constr c_F₂ into (F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ σ * A) =>
    rw [rpow_two (sqrt (_ + r ^ 2)), sq_sqrt (h_A_div_2π_add_r2_nonneg r A c_r c_R_lb)]
    rw [iff_eq_eq]; congr; ring_nf; field_simp; ring

#print trussDesignGP
-- minimize 2 * A * sqrt (w ^ 2 + h ^ 2)
--   subject to
--     c_r : 0 < r
--     c_F₁ : F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ σ * A
--     c_F₂ : F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ σ * A
--     c_hmin : hmin ≤ h
--     c_hmax : h ≤ hmax
--     c_wmin : wmin ≤ w
--     c_wmax : w ≤ wmax
--     c_A_lb : 0.21 * r ^ 2 ≤ A / (2 * π)
--     c_A_ub : sqrt (A / (2 * π) + r ^ 2) ≤ Rmax

instance : ChangeOfVariables
    fun ((h', w', r', A') : ℝ × ℝ × ℝ × ℝ) => (exp h', exp w', exp r', exp A') :=
  { inv := fun (h, w, r, A) => (log h, log w, log r, log A),
    condition := fun (h', w', r', A') => 0 < h' ∧ 0 < w' ∧ 0 < r' ∧ 0 < A',
    property := fun (h', w', r', A') ⟨hh', hw', hr', hA'⟩ => by
      simp [exp_log hh', exp_log hw', exp_log hr', exp_log hA'] }

equivalence' eqv₂/trussDesignConvex (hmin hmax : ℝ) (hmin_pos : 0 < hmin)
    (hmin_le_hmax : hmin ≤ hmax) (wmin wmax : ℝ) (wmin_pos : 0 < wmin) (wmin_le_wmax : wmin ≤ wmax)
    (Rmax σ F₁ F₂ : ℝ) : trussDesignGP hmin hmax wmin wmax Rmax σ F₁ F₂ := by
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
  conv_opt => dsimp
  rename_vars [h', w', r', A']
  remove_trivial_constrs

#print trussDesignConvex
-- optimization (h' : ℝ) (w' : ℝ) (r' : ℝ) (A' : ℝ)
--   minimize 2 * rexp A' * sqrt (rexp w' ^ 2 + rexp h' ^ 2)
--   subject to
--     c_F₁ : F₁ * sqrt (rexp w' ^ 2 + rexp h' ^ 2) / (2 * rexp h') ≤ σ * rexp A'
--     c_F₂ : F₂ * sqrt (rexp w' ^ 2 + rexp h' ^ 2) / (2 * rexp w') ≤ σ * rexp A'
--     c_hmin : hmin ≤ rexp h'
--     c_hmax : rexp h' ≤ hmax
--     c_wmin : wmin ≤ rexp w'
--     c_wmax : rexp w' ≤ wmax
--     c_A_lb : 0.21 * rexp r' ^ 2 ≤ rexp A' / (2 * π)
--     c_A_ub : sqrt (rexp A' / (2 * π) + rexp r' ^ 2) ≤ Rmax

-- We split these two steps, to make speed up backward map creation as there are ~80 pre-DCP steps
-- which need to be simplified into a single map (which should be just `id`).

equivalence eqv₃/trussDesignDCP (hmin hmax : ℝ) (hmin_pos : 0 < hmin) (hmin_le_hmax : hmin ≤ hmax)
    (wmin wmax : ℝ) (wmin_pos : 0 < wmin) (wmin_le_wmax : wmin ≤ wmax) (Rmax : ℝ)
    (Rmax_pos : 0 < Rmax) (σ : ℝ) (σ_pos : 0 < σ) (F₁ : ℝ) (F₁_pos : 0 < F₁) (F₂ : ℝ)
    (F₂_pos : 0 < F₂) : trussDesignConvex hmin hmax hmin_pos hmin_le_hmax wmin wmax wmin_pos
      wmin_le_wmax Rmax σ F₁ F₂ := by
  -- Apply pre-DCP.
  pre_dcp

#print trussDesignDCP
-- minimize log (rexp (2 * h') + rexp (2 * w')) + 2 * (log 2 + A')
--   subject to
--     c_F₁ : 1 / 2 * log (rexp (2 * h') + rexp (2 * w')) ≤ log σ + A' - (log (F₁ / 2) - h')
--     c_F₂ : 1 / 2 * log (rexp (2 * h') + rexp (2 * w')) ≤ log σ + (w' + A') - log (F₂ / 2)
--     c_hmin : log hmin ≤ h'
--     c_hmax : rexp h' ≤ hmax
--     c_wmin : log wmin ≤ w'
--     c_wmax : rexp w' ≤ wmax
--     c_A_lb : log (21 / 100) + 2 * r' ≤ A' - log (2 * π)
--     c_A_ub : rexp A' ≤ (Rmax * Rmax - rexp (2 * r')) * (2 * π)

-- We provide concrete values and solve the problem.

@[optimization_param]
def hminₚ : ℝ := 1

@[optimization_param]
def hmaxₚ : ℝ := 100

@[simp high]
lemma hminₚ_pos : 0 < hminₚ := by
  unfold hminₚ; norm_num

lemma hminₚ_le_hmaxₚ : hminₚ ≤ hmaxₚ := by
  unfold hminₚ hmaxₚ; norm_num

@[optimization_param]
def wminₚ : ℝ := 1

@[optimization_param]
def wmaxₚ : ℝ := 100

@[simp high]
lemma wminₚ_pos : 0 < wminₚ := by
  unfold wminₚ; norm_num

lemma wminₚ_le_wmaxₚ : wminₚ ≤ wmaxₚ := by
  unfold wminₚ wmaxₚ; norm_num

@[optimization_param]
def Rmaxₚ : ℝ := 10

@[simp high]
lemma Rmaxₚ_pos : 0 < Rmaxₚ := by
  unfold Rmaxₚ; norm_num

@[optimization_param]
def σₚ : ℝ := 0.5

@[simp high]
lemma σₚ_pos : 0 < σₚ := by
  unfold σₚ; norm_num

@[optimization_param]
def F₁ₚ : ℝ := 10

@[simp high]
lemma F₁ₚ_pos : 0 < F₁ₚ := by
  unfold F₁ₚ; norm_num

@[optimization_param]
def F₂ₚ : ℝ := 20

@[simp high]
lemma F₂ₚ_pos : 0 < F₂ₚ := by
  unfold F₂ₚ; norm_num

solve trussDesignDCP hminₚ hmaxₚ hminₚ_pos hminₚ_le_hmaxₚ wminₚ wmaxₚ wminₚ_pos wminₚ_le_wmaxₚ Rmaxₚ
  Rmaxₚ_pos σₚ σₚ_pos F₁ₚ F₁ₚ_pos F₂ₚ F₂ₚ_pos

-- There are two non-trivial backward maps here, one from `eqv₁` and one from `eqv₂`, so we need to
-- apply both of them.

def eqv₁.backward_mapₚ := eqv₁.backward_map hminₚ.float hmaxₚ.float wminₚ.float wmaxₚ.float
  Rmaxₚ.float σₚ.float F₁ₚ.float F₂ₚ.float

def eqv₂.backward_mapₚ := eqv₂.backward_map hminₚ.float hmaxₚ.float wminₚ.float wmaxₚ.float
  Rmaxₚ.float σₚ.float F₁ₚ.float F₂ₚ.float

def sol := eqv₁.backward_mapₚ (eqv₂.backward_mapₚ trussDesignDCP.solution)

-- Finally, we obtain the optimal height, width, inner radius, and outer radius.

def hₚ_opt := sol.1
def wₚ_opt := sol.2.1
def rₚ_opt := sol.2.2.1
def Rₚ_opt := sol.2.2.2

#eval hₚ_opt -- 1.000000
#eval wₚ_opt -- 1.000517
#eval rₚ_opt -- 0.010162
#eval Rₚ_opt -- 2.121443

def valueₚ :=
  let pi := 2 * Float.acos 0;
  let Aₚ_opt := 2 * pi * (Rₚ_opt ^ 2 - rₚ_opt ^ 2);
  2 * Aₚ_opt * Float.sqrt (wₚ_opt ^ 2 + hₚ_opt ^ 2)

#eval valueₚ -- 79.999976

end TrussDesign

end
