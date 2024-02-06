import CvxLean.Lib.Math.LinearAlgebra.Matrix.PosDef

/-!
Definitions needed for `Examples/CovarianceEstimation.lean`.
-/

noncomputable section CovarianceEstimation

open Real

open Matrix

open BigOperators

def Matrix.quadForm {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ R.mulVec x

def gaussianPdf {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / sqrt (((2 * π) ^ n) * R.det)) * exp (- R⁻¹.quadForm x / 2)

def covarianceMatrix {N n : ℕ} (y : Fin N → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j : Fin n => (∑ k : Fin N, y k i * y k j) / N

lemma gaussianPdf_pos {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (h : R.PosDef) :
    0 < gaussianPdf R y := by
  refine' mul_pos (div_pos zero_lt_one (sqrt_pos.2 (mul_pos _ h.det_pos))) (exp_pos _)
  exact (pow_pos (mul_pos (by positivity) pi_pos) n)

lemma prod_gaussianPdf_pos {N n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) (y : Fin N → Fin n → ℝ)
    (h : R.PosDef) : 0 < ∏ i : Fin N, gaussianPdf R (y i) :=
  Finset.prod_pos (fun _ _ => gaussianPdf_pos _ _ h)

lemma log_prod_gaussianPdf {N n : ℕ} (y : Fin N → Fin n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.PosDef) : log (∏ i : Fin N, gaussianPdf R (y i)) =
    ∑ i : Fin N, (- (log (sqrt ((2 * π) ^ n)) + log (sqrt R.det)) + - R⁻¹.quadForm (y i) / 2) := by
  have : ∀ i,
    i ∈ Finset.univ → gaussianPdf R (y i) ≠ 0 := fun i _ => ne_of_gt (gaussianPdf_pos _ _ hR)
  have sqrt_2_pi_n_R_det_ne_zero: sqrt ((2 * π) ^ n * R.det) ≠ 0 := by
    refine' ne_of_gt (sqrt_pos.2 (mul_pos _ hR.det_pos))
    exact (pow_pos (mul_pos (by positivity) pi_pos) _)
  rw [log_prod Finset.univ (fun i => gaussianPdf R (y i)) this]
  unfold gaussianPdf
  apply congr_arg (Finset.sum Finset.univ)
  ext i
  rw [log_mul, log_div, sqrt_mul, log_mul, log_exp, log_one, zero_sub]
  simp [rpow_eq_pow]
  exact ne_of_gt (sqrt_pos.2 (pow_pos (mul_pos (by positivity) pi_pos) _))
  exact ne_of_gt (sqrt_pos.2 hR.det_pos)
  exact pow_nonneg (mul_nonneg (by positivity) (le_of_lt pi_pos)) _
  norm_num
  exact sqrt_2_pi_n_R_det_ne_zero
  exact div_ne_zero (by norm_num) sqrt_2_pi_n_R_det_ne_zero
  exact exp_ne_zero _

lemma sum_quadForm {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} (y : Fin m → Fin n → ℝ) :
    ∑ i, R.quadForm (y i) = m * (covarianceMatrix y * Rᵀ).trace := by
  by_cases h : m = 0
  { subst h; simp }
  simp only [Matrix.quadForm, Matrix.trace, covarianceMatrix, diag, mul_apply, Finset.sum_mul,
    Finset.sum_div]
  simp_rw [@Finset.sum_comm _ (Fin m), Finset.mul_sum]
  apply congr_arg
  ext i
  unfold dotProduct
  have : (m : ℝ) ≠ 0 := by simp [h]
  simp_rw [← mul_assoc, mul_div_cancel' _ this]
  apply congr_arg
  ext j
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply congr_arg
  unfold Matrix.mulVec
  unfold dotProduct
  simp only [mul_comm (R _ _)]
  congr

lemma Real.inverse_eq_inv (a : ℝ) : Ring.inverse a = a⁻¹ := by simp

end CovarianceEstimation
