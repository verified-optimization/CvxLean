import CvxLean

/-!
# Case study: Fitting a sphere to data

See exercise 8.16 in https://github.com/cvxgrp/cvxbook_additional_exercises.
-/

noncomputable section

open CvxLean Minimization Real BigOperators Matrix Finset

section LeastSquares

def leastSquares {n : ℕ} (a : Fin n → ℝ) :=
  optimization (x : ℝ)
    minimize (∑ i, ((a i - x) ^ 2) : ℝ)

@[reducible]
def mean {n : ℕ} (a : Fin n → ℝ) : ℝ := (1 / n) * ∑ i, (a i)

/-- It is useful to rewrite the sum of squares in the following way to prove
`leastSquares_optimal_eq_mean`, following Marty Cohen's answer in
https://math.stackexchange.com/questions/2554243. -/
lemma leastSquares_alt_objFun {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ) :
  (∑ i, ((a i - x) ^ 2)) = n * ((x - mean a) ^ 2 + (mean (a ^ 2) - (mean a) ^ 2)) := by
  calc
  -- 1) Σ (aᵢ - x)² = Σ (aᵢ² - 2aᵢx + x²)
  _ = ∑ i, ((a i) ^ 2 - 2 * (a i) * x + (x ^ 2)) := by
    congr; funext i; simp; ring
  -- 2) ... = Σ aᵢ² - 2xΣ aᵢ + nx²
  _ = ∑ i, ((a i) ^ 2) - 2 * x * ∑ i, (a i) + n * (x ^ 2) := by
    rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum]; simp [sum_const]; ring
  -- 3) ... = n{a²} - 2xn{a} + nx²
  _ = n * mean (a ^ 2) - 2 * x * n * mean a + n * (x ^ 2) := by
    simp [mean]; field_simp; ring
  -- 4) ... = n((x - {a})² + ({a²} - {a}²))
  _ = n * ((x - mean a) ^ 2 + (mean (a ^ 2) - (mean a) ^ 2)) := by
    simp [mean]; field_simp; ring

/-- Key result about least squares: `x* = mean a`. -/
lemma leastSquares_optimal_eq_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ)
  (h : (leastSquares a).optimal x) : x = mean a := by
  simp [optimal, feasible, leastSquares] at h
  replace h : ∀ y, (x - mean a) ^ 2 ≤ (y - mean a) ^ 2  := by
    intros y
    have hy := h y
    have h_rw_x := leastSquares_alt_objFun hn a x
    have h_rw_y := leastSquares_alt_objFun hn a y
    simp only [rpow_two] at h_rw_x h_rw_y ⊢
    rwa [h_rw_x, h_rw_y, mul_le_mul_left (by positivity), add_le_add_iff_right] at hy
  have hmean := h (mean a)
  simp at hmean
  have h_sq_eq_zero := le_antisymm hmean (sq_nonneg _)
  rwa [sq_eq_zero_iff, sub_eq_zero] at h_sq_eq_zero

def leastSquaresVec {n : ℕ} (a : Fin n → ℝ) :=
  optimization (x : ℝ)
    minimize (Vec.sum ((a - Vec.const n x) ^ 2) : ℝ)

/-- Same as `leastSquares_optimal_eq_mean` in vector notation. -/
lemma leastSquaresVec_optimal_eq_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ)
  (h : (leastSquaresVec a).optimal x) : x = mean a := by
  apply leastSquares_optimal_eq_mean hn a
  simp [leastSquaresVec, leastSquares, optimal, feasible] at h ⊢
  intros y
  simp only [Vec.sum, Pi.pow_apply, Pi.sub_apply, Vec.const, rpow_two] at h
  exact h y

end LeastSquares

namespace FittingSphere

-- Dimension.
variable (n : ℕ)

-- Number of points.
variable (m : ℕ)

-- Given points.
variable (x : Fin m → Fin n → ℝ)

def fittingSphere :=
  optimization (c : Fin n → ℝ) (r : ℝ)
    minimize (∑ i, (‖(x i) - c‖ ^ 2 - r ^ 2) ^ 2 : ℝ)
    subject to
      h₁ : 0 < r

instance : ChangeOfVariables fun ((c, t) : (Fin n → ℝ) × ℝ) => (c, sqrt (t + ‖c‖ ^ 2)) :=
  { inv := fun (c, r) => (c, r ^ 2 - ‖c‖ ^ 2),
    condition := fun (_, r) => 0 ≤ r,
    property := fun ⟨c, r⟩ h => by simp [sqrt_sq h] }

equivalence' eqv/fittingSphereT (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere n m x := by
  -- Change of variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (ct : (Fin n → ℝ) × ℝ) => (ct.1, sqrt (ct.2 + ‖ct.1‖ ^ 2)))
    . rintro _ h; exact le_of_lt h
  rename_vars [c, t]
  -- Clean up.
  conv_constr h₁ => dsimp
  conv_obj => dsimp
  -- Rewrite objective.
  equivalence_step =>
    apply Equivalence.rewrite_objFun
      (g := fun (ct : (Fin n → ℝ) × ℝ) =>
        Vec.sum (((Vec.norm x) ^ 2 - 2 * (Matrix.mulVec x ct.1) - Vec.const m ct.2) ^ 2))
    . rintro ⟨c, t⟩ h
      dsimp at h ⊢; simp [Vec.sum, Vec.norm, Vec.const]; congr; funext i; congr 1;
      rw [norm_sub_sq (𝕜 := ℝ) (E := Fin n → ℝ), sq_sqrt (rpow_two _ ▸ le_of_lt (sqrt_pos.mp h))]
      simp [mulVec, inner, dotProduct]
  rename_vars [c, t]

#print fittingSphereT
-- optimization (c : Fin n → ℝ) (t : ℝ)
--   minimize Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2)
--   subject to
--     h₁ : 0 < sqrt (t + ‖c‖ ^ 2)

-- Next, we proceed to remove the non-convex constraint by arguing that any (non-trivial) point that
-- minimizes the objective function without the constraint, also satisfies the constraint. We define
-- the problem directly, but note that we could also remove the constraint using the `relaxation`
-- command.

def fittingSphereConvex (n m : ℕ) (x : Fin m → Fin n → ℝ) :=
  optimization (c : Fin n → ℝ) (t : ℝ)
    minimize (Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2) : ℝ)

/-- If the squared error is zero, then `aᵢ = x`. -/
lemma vec_squared_norm_error_eq_zero_iff {n m : ℕ} (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i, ‖a i - x‖ ^ 2 = 0 ↔ ∀ i, a i = x := by
  simp [rpow_two]
  rw [sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  . intros h i
    have hi := h i (by simp)
    rwa [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hi
  . intros h i _
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]
    exact h i

/-- This tells us that solving the relaxed problem is sufficient for optimal points if the solution
is non-trivial. -/
lemma optimal_convex_implies_optimal_t (hm : 0 < m) (c : Fin n → ℝ) (t : ℝ)
  (h_nontrivial : x ≠ Vec.const m c)
  (h_opt : (fittingSphereConvex n m x).optimal (c, t)) : (fittingSphereT n m x).optimal (c, t) := by
  simp [fittingSphereT, fittingSphereConvex, optimal, feasible] at h_opt ⊢
  constructor
  . let a := Vec.norm x ^ 2 - 2 * mulVec x c
    have h_ls : optimal (leastSquaresVec a) t := by
      refine ⟨trivial, ?_⟩
      intros y _
      simp [objFun, leastSquaresVec]
      exact h_opt c y
    -- Apply key result about least squares to `a` and `t`.
    have h_t_eq := leastSquaresVec_optimal_eq_mean hm a t h_ls
    have h_c2_eq : ‖c‖ ^ 2 = (1 / m) * ∑ i : Fin m, ‖c‖ ^ 2 := by
      simp [sum_const]
      field_simp; ring
    have h_t_add_c2_eq : t + ‖c‖ ^ 2 = (1 / m) * ∑ i, ‖(x i) - c‖ ^ 2 := by
      rw [h_t_eq]; dsimp [mean]
      rw [h_c2_eq, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      congr; funext i; rw [← mul_add]
      congr; simp [Vec.norm]
      rw [norm_sub_sq (𝕜 := ℝ) (E := Fin n → ℝ)]
      congr
    -- We use the result to establish that `t + ‖c‖ ^ 2` is non-negative.
    have h_t_add_c2_nonneg : 0 ≤ t + ‖c‖ ^ 2 := by
      rw [h_t_add_c2_eq]
      apply mul_nonneg (by norm_num)
      apply sum_nonneg
      intros i _
      rw [rpow_two]
      exact sq_nonneg _
    cases (lt_or_eq_of_le h_t_add_c2_nonneg) with
    | inl h_t_add_c2_lt_zero =>
        -- If it is positive, we are done.
        convert h_t_add_c2_lt_zero; simp
    | inr h_t_add_c2_eq_zero =>
        -- Otherwise, it contradicts the non-triviality assumption.
        exfalso
        rw [h_t_add_c2_eq, zero_eq_mul] at h_t_add_c2_eq_zero
        rcases h_t_add_c2_eq_zero with (hc | h_sum_eq_zero)
        . simp at hc; linarith
        rw [vec_squared_norm_error_eq_zero_iff] at h_sum_eq_zero
        apply h_nontrivial
        funext i
        exact h_sum_eq_zero i
  . intros c' x' _
    exact h_opt c' x'

/-- We express the nontriviality condition only in terms of `x` so that it can be checked. -/
lemma non_triviality_condition (c : Fin n → ℝ) (hx : ∃ i j, x i ≠ x j) : x ≠ Vec.const m c := by
  intros h
  conv at hx => congr; ext i; rw [← not_forall]
  rw [← not_forall] at hx
  apply hx
  intros i j
  rw [congr_fun h i, congr_fun h j]
  simp [Vec.const]

/-- We show that we have a reduction via the identity map. -/
def red (hm : 0 < m) (hx : ∃ i j, x i ≠ x j) :
    (fittingSphereT n m x) ≼ (fittingSphereConvex n m x) :=
  { psi := id,
    psi_optimality := fun (c, t) h_opt => by
      have h_nontrivial := non_triviality_condition n m x c hx
      exact optimal_convex_implies_optimal_t n m x hm c t h_nontrivial h_opt }

#print fittingSphereConvex
-- optimization (c : Fin n → ℝ) (t : ℝ)
--   minimize Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2)

-- We proceed to solve the problem on a concrete example.
-- https://github.com/cvxgrp/cvxbook_additional_exercises/blob/main/python/sphere_fit_data.py

@[optimization_param]
def nₚ := 2

@[optimization_param]
def mₚ := 10

@[optimization_param]
def xₚ : Fin mₚ → Fin nₚ → ℝ := Matrix.transpose <| ![
  ![1.824183228637652032e+00, 1.349093690455489103e+00, 6.966316403935147727e-01,
    7.599387854623529392e-01, 2.388321695850912363e+00, 8.651370608981923116e-01,
    1.863922545015865406e+00, 7.099743941474848663e-01, 6.005484882320809570e-01,
    4.561429569892232472e-01],
  ![-9.644136284187876385e-01, 1.069547315003422927e+00, 6.733229334437943470e-01,
    7.788072961810316164e-01, -9.467465278344706636e-01, -8.591303443863639311e-01,
    1.279527420871080956e+00, 5.314829019311283487e-01, 6.975676079749143499e-02,
    -4.641873429414754559e-01]]

-- We use the `solve` command on the data above.

solve fittingSphereConvex nₚ mₚ xₚ

-- Finally, we recover the solution to the original problem.

def sol := eqv.backward_map nₚ mₚ xₚ.float fittingSphereConvex.solution

def cₚ_opt := sol.1
def rₚ_opt := sol.2

#eval cₚ_opt -- ![1.664863, 0.031932]
#eval rₚ_opt -- 1.159033

end FittingSphere

end
