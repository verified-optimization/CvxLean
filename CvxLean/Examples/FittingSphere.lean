import CvxLean

/-!
# Case study: Fitting a sphere to data

See exercise 8.16 in https://github.com/cvxgrp/cvxbook_additional_exercises.
-/

noncomputable section

open CvxLean Minimization Real BigOperators Matrix Finset

section LeastSquares

/- We first need some preliminaries on least squares. -/

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
      h₁ : 0 ≤ r

-- Changes of variables ensuring bijection, which must also add the condition on `E` in the
-- equivalence. TODO: Move to `CvxLean` core.

structure ChangeOfVariablesBij {D E} (c : E → D) where
  c_inv : D → E
  cond_D : D → Prop
  cond_E : E → Prop
  prop_D : ∀ x, cond_D x → c (c_inv x) = x
  prop_E : ∀ y, cond_E y → c_inv (c y) = y

@[equiv]
def ChangeOfVariablesBij.toEquivalence {D E R} [Preorder R] {f : D → R} {cs : D → Prop} (c : E → D)
    (cov : ChangeOfVariablesBij c)
    (hD : ∀ x, cs x → cov.cond_D x)
    (hE : ∀ x, cs x → cov.cond_E (cov.c_inv x)) :
    ⟨f, cs⟩ ≡ ⟨fun y => f (c y), fun y => cs (c y) ∧ cov.cond_E y⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => cov.c_inv x
    psi := fun y => c y
    phi_feasibility := fun x hx => by simp [feasible, cov.prop_D x (hD x hx)]; exact ⟨hx, hE x hx⟩
    psi_feasibility := fun y ⟨hy, _⟩ => hy
    phi_optimality := fun x hx => by simp [cov.prop_D x (hD x hx)]
    psi_optimality := fun y _ => by simp }

def covBij {n} : ChangeOfVariablesBij
    (fun ((c, t) : (Fin n → ℝ) × ℝ) => (c, sqrt (t + ‖c‖ ^ 2))) :=
  { c_inv := fun (c, r) => (c, r ^ 2 - ‖c‖ ^ 2),
    cond_D := fun (_, r) => 0 ≤ r,
    cond_E := fun (c, t) => 0 ≤ t + ‖c‖ ^ 2,
    prop_D := fun (c, r) h => by simp [sqrt_sq h],
    prop_E := fun (c, t) h => by simp at h; simp [sq_sqrt h] }

equivalence* eqv/fittingSphereT (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere n m x := by
  -- Change of variables (bijective) + some clean up.
  -- TODO: Do this with `change_of_variables` (or a new command `change_of_variables_bij`).
  equivalence_step =>
    apply ChangeOfVariablesBij.toEquivalence
      (fun (ct : (Fin n → ℝ) × ℝ) => (ct.1, sqrt (ct.2 + ‖ct.1‖ ^ 2))) covBij
    · rintro cr h; exact h
    . rintro ct _; simp [covBij, sq_nonneg]
  rename_vars [c, t]
  rename_constrs [h₁, h₂]
  conv_constr h₁ => dsimp
  conv_constr h₂ => dsimp [covBij]
  -- Rewrite objective.
  rw_obj into (Vec.sum (((Vec.norm x) ^ 2 - 2 * (Matrix.mulVec x c) - Vec.const m t) ^ 2)) =>
    simp [Vec.sum, Vec.norm, Vec.const]; congr; funext i; congr 1;
    rw [norm_sub_sq (𝕜 := ℝ) (E := Fin n → ℝ), sq_sqrt (rpow_two _ ▸ h₂)]
    simp [mulVec, inner, dotProduct]
  -- Remove redundant h₁.
  remove_constr h₁ => exact sqrt_nonneg _

#print fittingSphereT
-- optimization (c : Fin n → ℝ) (t : ℝ)
--   minimize Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2)
--   subject to
--     h₂ : 0 ≤ t + ‖c‖ ^ 2

-- Next, we proceed to remove the non-convex constraint by arguing that any point that minimizes the
-- objective function without the constraint, also satisfies the constraint. We define the problem
-- directly, but note that we could also remove the constraint using the `reduction` command.

def fittingSphereConvex (n m : ℕ) (x : Fin m → Fin n → ℝ) :=
  optimization (c : Fin n → ℝ) (t : ℝ)
    minimize (Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2) : ℝ)

/-- This tells us that solving the relaxed problem is sufficient (i.e., it is a valid reduction). -/
lemma optimal_convex_implies_optimal_t (hm : 0 < m) (c : Fin n → ℝ) (t : ℝ)
    (h_opt : (fittingSphereConvex n m x).optimal (c, t)) :
    (fittingSphereT n m x).optimal (c, t) := by
  simp [fittingSphereT, fittingSphereConvex, optimal, feasible] at h_opt ⊢
  constructor
  -- Feasibility.
  · let a := Vec.norm x ^ 2 - 2 * mulVec x c
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
    rw [← rpow_two, h_t_add_c2_eq]
    apply mul_nonneg (by norm_num)
    apply sum_nonneg
    intros i _
    rw [rpow_two]
    exact sq_nonneg _
  -- Optimality.
  · intros c' x' _
    exact h_opt c' x'

/-- We show that we have a reduction via the identity map. -/
def red (hm : 0 < m) : (fittingSphereT n m x) ≼ (fittingSphereConvex n m x) :=
  { psi := id,
    psi_optimality := fun (c, t) h_opt => optimal_convex_implies_optimal_t n m x hm c t h_opt }

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
