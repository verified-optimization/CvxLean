import CvxLean.Lib.Missing.Vec
import CvxLean.Syntax.Minimization
import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Command.Reduction
import CvxLean.Command.Solve

open Real
open Minimization
open CvxLean
open Matrix

noncomputable def problem (n : ℕ) (N : ℕ) (α : ℝ) (y : Fin N → Fin n →  ℝ) := 
  optimization (R : Matrix (Fin n) (Fin n) ℝ)
    maximize (∏ i, gaussianPdf R (y i))
    subject to 
      c_pos_def : R.PosDef
      c_sparse : R⁻¹.abs.sum <= α

reduction reduction₁₂/problem₂ (n : ℕ) (N : ℕ) (α : ℝ) (y : Fin N → Fin n → ℝ) :
  problem n N α y := by
  simp only [problem]
  -- apply logarithm to objective:
  apply map_objective ℝ ℝ _ (fun x => - log (-x))
  · intros R S hR hS h
    apply neg_le_neg
    simp only [maximizeNeg] at h
    rwa [neg_negₓ, neg_negₓ, 
      @neg_le_neg_iff Real _ _ (OrderedAddCommGroup.to_covariant_class_left_le _) _,
      log_le_log] at h
    exact prod_gaussian_pdf_pos S y hS.1
    exact prod_gaussian_pdf_pos R y hR.1
  simp only [Function.comp, neg_negₓ, maximizeNeg]
  -- move logarithm and sum inward:
  apply rewrite_objective
  · intros R hR
    simp only [log_prod_gaussianPdf _ R hR.1,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_div]
    rewrite [Finset.sum_const, Finset.sum_const, Finset.card_fin]
    rw [← Finset.sum_div, sum_quad_form, @Real.log_sqrt (det R)]
    apply hR.1.pos_semidef.det_nonneg
  -- variable change using matrix inverse:
  apply map_domain (f := (·⁻¹)) (g := (·⁻¹))
  · intros R hR
    simp only [nonsing_inv_nonsing_inv R hR.1.is_unit_det]
  -- dissolve matrix inverse:
  simp only [Function.comp, Matrix.posdef_inv_iff_posdef]
  apply rewrite_objective
  · intros R hR
    rewrite [nonsing_inv_nonsing_inv R (hR.1.is_unit_det),
      Matrix.det_nonsing_inv]
    rewrite [Real.inverse_eq_inv, Real.log_inv]
    have : (bit0 One.one : ℝ) = 2 := by rw [← one_add_one_eq_two]; rfl
    simp only [this]
    rfl
  apply rewrite_constraints
  · intros R
    rw [And.congr_right_iff]
    intro hR
    rw [nonsing_inv_nonsing_inv R hR.is_unit_det]

#print problem₂

set_option maxHeartbeats 20000000
solve problem₂ 2 4 1 ![![0,2],![2,0],![-2,0],![0,-2]]

#print problem₂.reduced

#eval problem₂.status
#eval problem₂.value
#print problem₂.solution
