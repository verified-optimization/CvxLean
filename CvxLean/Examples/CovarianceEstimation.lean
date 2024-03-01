import CvxLean

/-!
# Case study: Sparse covariance estimation for Gaussian variables

See https://www.cvxpy.org/examples/applications/sparse_covariance_est.html.
-/

namespace CovarianceEstimation

open CvxLean Minimization Real BigOperators Matrix

noncomputable def covEstimation (n : ℕ) (N : ℕ) (α : ℝ) (y : Fin N → Fin n →  ℝ) :=
  optimization (R : Matrix (Fin n) (Fin n) ℝ)
    maximize (∏ i, gaussianPdf R (y i))
    subject to
      c_pos_def : R.PosDef
      c_sparse : R⁻¹.abs.sum ≤ α

reduction* red/covEstimationConvex (n : ℕ) (N : ℕ) (α : ℝ) (y : Fin N → Fin n → ℝ) :
  covEstimation n N α y := by
  -- Change objective function.
  reduction_step =>
    apply Reduction.map_objFun_of_order_reflecting (g := fun x => -log (-x))
    · intros R S hR hS h
      apply neg_le_neg
      simp only [maximizeNeg] at h
      rwa [neg_neg, neg_neg, neg_le_neg_iff, log_le_log_iff] at h
      exact prod_gaussianPdf_pos S y hS.1
      exact prod_gaussianPdf_pos R y hR.1
  conv_opt =>
    simp only [Function.comp, neg_neg, maximizeNeg]
  -- Move logarithm and sum inward.
  reduction_step =>
    apply Reduction.rewrite_objFun
    · intros R hR
      simp only [log_prod_gaussianPdf _ R hR.1,
        Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_div]
      rewrite [Finset.sum_const, Finset.sum_const, Finset.card_fin]
      rw [← Finset.sum_div, sum_quadForm, @Real.log_sqrt (det R)]
      apply hR.1.posSemidef.det_nonneg
  -- Change of variables using matrix inverse.
  reduction_step =>
    apply Reduction.map_domain (fwd := (·⁻¹)) (bwd := (·⁻¹))
    · intros R hR
      simp only [nonsing_inv_nonsing_inv R hR.1.isUnit_det]
  -- Dissolve matrix inverse.
  conv_opt =>
    simp only [Function.comp, Matrix.PosDef_inv_iff_PosDef]
  reduction_step =>
    apply Reduction.rewrite_objFun
    · intros R hR
      rewrite [nonsing_inv_nonsing_inv R (hR.1.isUnit_det),
        Matrix.det_nonsing_inv]
      rewrite [Real.inverse_eq_inv, Real.log_inv]
      rfl
  reduction_step =>
    apply Reduction.rewrite_constraints
    · intros R
      rw [and_congr_right_iff]
      intro hR
      rw [nonsing_inv_nonsing_inv R hR.isUnit_det]

#print covEstimationConvex
-- optimization (R : Matrix (Fin n) (Fin n) ℝ)
--   minimize
--     -(-(N • log (sqrt ((2 * π) ^ n)) + N • (-log (det R) / 2)) +
--         -(↑N * trace ((covarianceMatrix fun x => y x) * Rᵀ) / 2))
--   subject to
--     c_pos_def : PosDef R
--     c_sparse : sum (Matrix.abs R) ≤ α

-- We solve the problem for a simple example.

@[optimization_param, reducible]
def nₚ : ℕ := 2

@[optimization_param, reducible]
def Nₚ : ℕ := 4

@[optimization_param]
def αₚ : ℝ := 1

@[optimization_param]
def yₚ : Fin Nₚ → Fin nₚ → ℝ := ![![0, 2], ![2, 0], ![-2, 0], ![0, -2]]

solve covEstimationConvex nₚ Nₚ αₚ yₚ

#print covEstimationConvex.reduced
-- minimize
--     -(-(Nₚ • log (sqrt ((2 * π) ^ nₚ)) + Nₚ • (-Vec.sum t.0 / 2)) +
--         -(↑Nₚ * trace ((covarianceMatrix fun i => yₚ i) * Rᵀ) / 2))
--   subject to
--     _ : Real.posOrthCone (αₚ - sum T.2)
--     _ : Vec.expCone t.0 1 (diag Y.1)
--     _ :
--       PSDCone
--         (let Z := toUpperTri Y.1;
--         let D := diagonal (diag Y.1);
--         let X := fromBlocks D Z Zᵀ R;
--         X)
--     _ : Matrix.posOrthCone (T.2 - R)
--     _ : Matrix.posOrthCone (T.2 + R)

#eval covEstimationConvex.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval covEstimationConvex.value    -- 14.124098
#eval covEstimationConvex.solution -- ![![0.499903, 0.000000], ![0.000000, 0.499905]]

-- We recover the optimal solution in the original problem.

def Rₚ_opt := red.backward_map nₚ Nₚ αₚ.float yₚ.float covEstimationConvex.solution

#eval Rₚ_opt -- !![2.000240, -0.000000; -0.000000, 2.000232]

end CovarianceEstimation
