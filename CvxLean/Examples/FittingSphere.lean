import CvxLean

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
  have hz := le_antisymm hmean (sq_nonneg _)
  rwa [sq_eq_zero_iff, sub_eq_zero] at hz

def Vec.leastSquares {n : ℕ} (a : Fin n → ℝ) :=
  optimization (x : ℝ)
    minimize (Vec.sum ((a - Vec.const n x) ^ 2) : ℝ)

/-- Same as `leastSquares_optimal_eq_mean` in vector notation. -/
lemma vec_leastSquares_optimal_eq_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ)
  (h : (Vec.leastSquares a).optimal x) : x = mean a := by
  apply leastSquares_optimal_eq_mean hn a
  simp [Vec.leastSquares, leastSquares, optimal, feasible] at h ⊢
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

instance : ChangeOfVariables fun (ct : (Fin n → ℝ) × ℝ) => (ct.1, sqrt (ct.2 + ‖ct.1‖ ^ 2)) :=
  { inv := fun (c, r) => (c, r ^ 2 - ‖c‖ ^ 2),
    condition := fun (_, t) => 0 ≤ t,
    property := fun ⟨c, t⟩ h => by simp [sqrt_sq h] }

equivalence eqv/fittingSphereT (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere n m x := by
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
      dsimp at h ⊢; simp [Vec.sum, Vec.norm, Vec.const]
      congr; funext i; congr 1;
      rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
      rw [sq_sqrt (rpow_two _ ▸ le_of_lt (sqrt_pos.mp <| h))]
      simp [mulVec, inner, dotProduct]
  rename_vars [c, t]

#print fittingSphereT

relaxation rel/fittingSphereConvex (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphereT n m x := by
  relaxation_step =>
    apply Relaxation.weaken_constraint (cs' := fun _ => True)
    . rintro ⟨c, t⟩ _; trivial

/-- If the squared error is zero, then `aᵢ = x`. -/
lemma vec_squared_norm_error_eq_zero_iff {n m : ℕ} (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i, ‖a i - x‖ ^ 2 = 0 ↔ ∀ i, a i = x := by
  simp [rpow_two]
  rw [sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  . intros h i
    have hi := h i (by simp)
    rw [sq_eq_zero_iff, @norm_eq_zero _ (PiLp.normedAddCommGroup _ _).toNormedAddGroup] at hi
    rwa [sub_eq_zero] at hi
  . intros h i _
    rw [sq_eq_zero_iff, @norm_eq_zero _ (PiLp.normedAddCommGroup _ _).toNormedAddGroup, sub_eq_zero]
    exact h i

/-- This tells us that solving the relaxed problem is sufficient for optimal points if the solution
is non-trivial. -/
lemma optimal_relaxed_implies_optimal (hm : 0 < m) (c : Fin n → ℝ) (t : ℝ)
  (h_nontrivial : x ≠ Vec.const m c)
  (h_opt : (fittingSphereConvex n m x).optimal (c, t)) : (fittingSphereT n m x).optimal (c, t) := by
  simp [fittingSphereT, fittingSphereConvex, optimal, feasible] at h_opt ⊢
  constructor
  . let a := Vec.norm x ^ 2 - 2 * mulVec x c
    have h_ls : optimal (Vec.leastSquares a) t := by
      refine ⟨trivial, ?_⟩
      intros y _
      simp [objFun, Vec.leastSquares]
      exact h_opt c y
    -- Apply key result about least squares to `a` and `t`.
    have ht_eq := vec_leastSquares_optimal_eq_mean hm a t h_ls
    have hc2_eq : ‖c‖ ^ 2 = (1 / m) * ∑ i : Fin m, ‖c‖ ^ 2 := by
      simp [sum_const]
      field_simp; ring
    have ht : t + ‖c‖ ^ 2 = (1 / m) * ∑ i, ‖(x i) - c‖ ^ 2 := by
      rw [ht_eq]; dsimp [mean]
      rw [hc2_eq, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      congr; funext i; rw [← mul_add]
      congr; simp [Vec.norm]
      rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
      congr
    -- We use the result to establish that `t + ‖c‖ ^ 2` is non-negative.
    have h_tc2_nonneg : 0 ≤ t + ‖c‖ ^ 2 := by
      rw [ht]
      apply mul_nonneg (by norm_num)
      apply sum_nonneg
      intros i _
      rw [rpow_two]
      exact sq_nonneg _
    cases (lt_or_eq_of_le h_tc2_nonneg) with
    | inl h_tc2_lt_zero =>
        -- If it is positive, we are done.
        convert h_tc2_lt_zero; simp
    | inr h_tc2_eq_zero =>
        -- Otherwise, it contradicts the non-triviality assumption.
        exfalso
        rw [ht, zero_eq_mul] at h_tc2_eq_zero
        rcases h_tc2_eq_zero with (hc | h_sum_eq_zero)
        . simp at hc; linarith
        rw [vec_squared_norm_error_eq_zero_iff] at h_sum_eq_zero
        apply h_nontrivial
        funext i
        exact h_sum_eq_zero i
  . intros c' x' _
    exact h_opt c' x'

#print fittingSphereConvex

-- We proceed to solve the problem on a concrete example.
-- https://github.com/cvxgrp/cvxbook_additional_exercises/blob/main/python/sphere_fit_data.py

def nₚ := 2

def mₚ := 50

def xₚ : Fin mₚ → Fin nₚ → ℝ := Matrix.transpose <| ![
  ![1.824183228637652032e+00, 1.349093690455489103e+00, 6.966316403935147727e-01,
    7.599387854623529392e-01, 2.388321695850912363e+00, 8.651370608981923116e-01,
    1.863922545015865406e+00, 7.099743941474848663e-01, 6.005484882320809570e-01,
    4.561429569892232472e-01, 5.328296545713475663e-01, 2.138547819234526415e+00,
    1.906676474276197464e+00, 1.015547309536922516e+00, 8.765948388006337133e-01,
    1.648147347399247842e+00, 1.027902202451572045e+00, 2.145586297520478691e+00,
    1.793440421753045744e+00, 1.020535583041398908e+00, 8.977911075271942654e-01,
    1.530480229262339398e+00, 2.478088034137528872e-01, 2.617415807793897820e+00,
    2.081978553098443374e+00, 1.891226687205936452e+00, 8.222497927065576251e-01,
    5.803514604868882376e-01, 1.158670193449639063e+00, 6.016685032455900695e-01,
    5.605410828151705660e-01, 2.508815467550573164e+00, 2.230201413385580977e+00,
    1.170848897912992514e+00, 2.256355929901105561e+00, 6.686991510936428629e-01,
    2.040269595792217672e+00, 3.634166812924328749e-01, 5.418647611079159265e-01,
    6.631470058399455692e-01, 4.286142597532469622e-01, 2.155925078996823618e+00,
    2.379380016960549682e+00, 6.343212414048013947e-01, 1.469076407947448981e+00,
    1.225322035289937439e+00, 1.467602887401966871e+00, 9.345319187253748883e-01,
    1.985592768641736505e+00, 2.106896115090134636e+00],
  ![-9.644136284187876385e-01, 1.069547315003422927e+00, 6.733229334437943470e-01,
    7.788072961810316164e-01, -9.467465278344706636e-01, -8.591303443863639311e-01,
    1.279527420871080956e+00, 5.314829019311283487e-01, 6.975676079749143499e-02,
    -4.641873429414754559e-01, -2.094571396598311763e-01, -8.003479827938377866e-01,
    6.135280782546607137e-01, -9.961307468791747999e-01, -8.765215480412106297e-01,
    9.655406812422813179e-01, 1.011230180540185541e+00, 6.105416770440197372e-01,
    9.486552370654932620e-01, -9.863592657836954825e-01, 7.695327845100754516e-01,
    -1.060072365810699413e+00, -4.041043465424410952e-01, -2.352952920283236105e-01,
    7.560391050507236921e-01, -9.454246095204003053e-01, -5.303145312191936966e-01,
    5.979590038743245461e-01, -1.154309511133019717e+00, -6.123184171955468047e-01,
    -1.464683782538583889e-01, -1.839128688968104386e-01, 4.250070477845909744e-01,
    8.861864983476224200e-01, 3.927648421593328276e-01, -6.726102374256350824e-01,
    -1.047252884197514833e+00, 1.825096825995130845e-01, -4.482373962742914886e-01,
    5.115625649313135792e-01, 7.846201103116770548e-02, 6.006325432819290544e-01,
    -5.710733714464664157e-01, 4.725559971890586075e-01, -8.440290321502940118e-01,
    -1.003920890712479475e+00, -1.067089412136528637e+00, 7.909281966910661765e-01,
    -1.059509163675931065e+00, -7.136351632325785843e-01]]

solve fittingSphereConvex nₚ mₚ xₚ

end FittingSphere

end
