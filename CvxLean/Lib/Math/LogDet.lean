import Mathlib.LinearAlgebra.Matrix.LDL

import CvxLean.Lib.Math.SchurComplement
import CvxLean.Lib.Math.Subadditivity
import CvxLean.Lib.Math.LinearAlgebra.Matrix.Triangular
import CvxLean.Lib.Math.LinearAlgebra.Matrix.ToUpperTri
import CvxLean.Lib.Math.LinearAlgebra.Matrix.LDL

/-!
In this file we prove properties needed for the log-det-atom. We follow the proof in the MOSEK
documentation: https://docs.mosek.com/modeling-cookbook/sdo.html#log-determinant.

See `CvxLean.Tactic.DCP.Fns.LogDet`.
-/

namespace Matrix

open Matrix BigOperators

variable {n : Type} [Fintype n] [LinearOrder n] [LocallyFiniteOrderBot n]
variable {𝕜 : Type} [IsROrC 𝕜]
variable {A : Matrix n n ℝ} (hA : A.PosDef)

noncomputable instance LDL.invertible_diag : Invertible (LDL.diag hA) := by
  rw [LDL.diag_eq_lowerInv_conj]
  refine @invertibleMul _ _ _ _ (@invertibleMul _ _ _ _ _ hA.Invertible) _

open scoped Matrix ComplexOrder

@[simp]
lemma PosSemidef_zero : PosSemidef (0 : Matrix n n 𝕜) := by
  simp [PosSemidef]

lemma LogDetAtom.feasibility_PosDef {D Z : Matrix n n ℝ} (hD : D = LDL.diag hA)
    (hZ : Z = LDL.diag hA * (LDL.lower hA)ᵀ) : (fromBlocks D Z Zᵀ A).PosSemidef := by
  have h_D_eq : D = Z * A⁻¹ * Zᴴ :=
    calc D
      = D * D⁻¹ * D := by
          rw [hD, Matrix.mul_inv_of_invertible, Matrix.one_mul]
    _ = D * (LDL.lowerInv hA * A * (LDL.lowerInv hA)ᵀ)⁻¹ * Dᵀ := by
          erw [hD, LDL.diag, diagonal_transpose, ← LDL.diag, LDL.diag_eq_lowerInv_conj]
          rfl
    _ = D * (LDL.lower hA)ᵀ * A⁻¹ * (D * (LDL.lower hA)ᵀ)ᵀ := by
          simp only [hD, LDL.lower, transpose_mul, transpose_transpose, transpose_nonsing_inv,
            Matrix.mul_assoc, Matrix.mul_inv_rev]
    _ = Z * A⁻¹ * Zᴴ := by
          rw [hZ, hD]; rfl
  haveI := hA.Invertible
  erw [PosSemidef.fromBlocks₂₂ _ _ hA]
  simp [h_D_eq]

lemma LogDetAtom.feasibility_PosDef' {D Z Y : Matrix n n ℝ} (hY : Y = LDL.diag hA * (LDL.lower hA)ᵀ)
    (hD : D = diagonal Y.diag) (hZ : Z = Y.toUpperTri) : (fromBlocks D Z Zᵀ A).PosSemidef := by
  have hY_tri : upperTriangular Y
  { rw [hY]
    apply upperTriangular.mul
    apply BlockTriangular_diagonal
    apply lowerTriangular.transpose
    apply LDL.lowerTriangular_lower }
  haveI := hA.Invertible
  rw [hZ, hY_tri.toUpperTri_eq]
  apply LogDetAtom.feasibility_PosDef _ _ hY
  simp [hD, hY, LDL.diag]

lemma LDL.diagEntries_pos {A : Matrix n n ℝ} (hA: A.PosDef) (i : n) :
    0 < LDL.diagEntries hA i := by
  have : (LDL.lowerInv hA).det ≠ 0 := by simp [LDL.det_lowerInv hA]
  have : LDL.lowerInv hA i ≠ 0 := fun h =>
    this (Matrix.det_eq_zero_of_row_eq_zero i (λ j => congr_fun h j))
  exact hA.2 (LDL.lowerInv hA i) this

lemma LogDetAtom.solution_eq_atom {A : Matrix n n ℝ} (hA: A.PosDef) :
    ∑ i, Real.log (LDL.diagEntries hA i) = Real.log (A.det) := by
  conv => rhs; rw [(LDL.lower_conj_diag hA).symm]
  have heqsum := Real.log_prod Finset.univ (LDL.diagEntries hA)
    (fun i _ => ne_of_gt (LDL.diagEntries_pos hA i))
  simp [LDL.diag, heqsum.symm]

lemma LogDetAtom.feasibility_exp {A : Matrix n n ℝ} (hA: A.PosDef) (i : n) :
    LDL.diagEntries hA i ≤ ((LDL.diag hA) * ((LDL.lower hA)ᵀ)).diag i := by
  simp [LDL.diag]

lemma IsHermitian₁₁_of_IsHermitian_toBlock {A B C D : Matrix n n ℝ}
    (h : (fromBlocks A B C D).IsHermitian) : IsHermitian A := by
  ext i j; simpa using congr_fun (congr_fun h (Sum.inl i)) (Sum.inl j)

lemma IsHermitian₂₂_of_IsHermitian_toBlock {A B C D : Matrix n n ℝ}
    (h : (fromBlocks A B C D).IsHermitian) : IsHermitian D := by
  ext i j; simpa using congr_fun (congr_fun h (Sum.inr i)) (Sum.inr j)

lemma PosSemidef₁₁_of_PosSemidef_toBlock {A B C D : Matrix n n ℝ}
    (h : (fromBlocks A B C D).PosSemidef) : PosSemidef A :=
  ⟨IsHermitian₁₁_of_IsHermitian_toBlock h.1,
   fun x => by simpa [Matrix.fromBlocks_mulVec, star] using h.2 (Sum.elim x 0)⟩

lemma PosSemidef₂₂_of_PosSemidef_toBlock {A B C D : Matrix n n ℝ}
    (h : (fromBlocks A B C D).PosSemidef) :
    PosSemidef D :=
  ⟨IsHermitian₂₂_of_IsHermitian_toBlock h.1,
   fun x => by simpa [Matrix.fromBlocks_mulVec, star] using h.2 (Sum.elim 0 x)⟩

lemma LogDetAtom.optimality_D_posdef {t : n → ℝ} {Y Z D : Matrix n n ℝ}
    (ht : ∀ i, (t i).exp ≤ Y.diag i) (hD : D = Matrix.diagonal (Y.diag)) (_hZ : Z = Y.toUpperTri)
    (hPSD : (fromBlocks D Z Zᵀ A).PosSemidef) : D.PosDef := by
  have h_D_psd : D.PosSemidef := PosSemidef₁₁_of_PosSemidef_toBlock hPSD
  show D.PosDef
  { rw [h_D_psd.PosDef_iff_det_ne_zero, hD, det_diagonal, Finset.prod_ne_zero_iff]
    exact λ i _ => ne_of_gt (lt_of_lt_of_le ((t i).exp_pos) (ht i)) }

lemma LogDetAtom.optimality_Ddet_le_Adet {t : n → ℝ} {Y Z D : Matrix n n ℝ}
    (ht : ∀ i, (t i).exp ≤ Y.diag i) (hD : D = Matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
    (hPSD : (fromBlocks D Z Zᵀ A).PosSemidef) : D.det ≤ A.det := by
  by_cases h_nonempty : Nonempty n
  { have h_D_pd : D.PosDef := LogDetAtom.optimality_D_posdef ht hD hZ hPSD
    haveI h_D_invertible : Invertible D := h_D_pd.Invertible
    have h_Zdet : Z.det = D.det
    { rw [hZ, det_of_upperTriangular (upperTriangular_toUpperTri Y), hD, det_diagonal]
      simp [toUpperTri] }
    have h_ZDZ_semidef : (Zᴴ * D⁻¹ * Z).PosSemidef :=
      PosSemidef.conjTranspose_mul_mul D⁻¹ Z h_D_pd.nonsingular_inv.posSemidef
    have h_AZDZ_semidef : (A - Zᴴ * D⁻¹ * Z).PosSemidef :=
      (PosSemidef.fromBlocks₁₁ Z A h_D_pd).1 hPSD
    show D.det ≤ A.det
    { apply le_of_add_le_of_nonneg_left _ h_AZDZ_semidef.det_nonneg
      simpa [h_Zdet] using det_add_det_le_det_add _ _ h_ZDZ_semidef h_AZDZ_semidef } }
  { haveI h_empty := not_nonempty_iff.1 h_nonempty
    simp [Matrix.det_isEmpty] }

lemma LogDetAtom.cond_elim {t : n → ℝ} {Y Z D : Matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
    (hD : D = Matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
    (hPSD : (fromBlocks D Z Zᵀ A).PosSemidef) : A.PosDef := by
  have h_D_pd : D.PosDef := LogDetAtom.optimality_D_posdef ht hD hZ hPSD
  have h_A_psd : A.PosSemidef := PosSemidef₂₂_of_PosSemidef_toBlock hPSD
  have h_Ddet_le_Adet : D.det ≤ A.det := LogDetAtom.optimality_Ddet_le_Adet ht hD hZ hPSD
  have h_Adet_pos : 0 < A.det := lt_of_lt_of_le h_D_pd.det_pos h_Ddet_le_Adet
  rw [h_A_psd.PosDef_iff_det_ne_zero]
  apply ne_of_gt h_Adet_pos

lemma LogDetAtom.optimality {t : n → ℝ} {Y Z D : Matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
    (hD : D = Matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
    (hPSD : (fromBlocks D Z Zᵀ A).PosSemidef) : ∑ i, t i ≤ Real.log A.det := by
  have h_A_pd : A.PosDef := LogDetAtom.cond_elim ht hD hZ hPSD
  have h_Ddet_le_Adet : D.det ≤ A.det := LogDetAtom.optimality_Ddet_le_Adet ht hD hZ hPSD
  have h_Adet_pos: 0 < A.det := h_A_pd.det_pos
  rw [← Real.exp_le_exp, Real.exp_sum, Real.exp_log h_Adet_pos]
  apply le_trans (Finset.prod_le_prod (fun i _ => le_of_lt ((t i).exp_pos)) (fun i _ => ht i))
  convert h_Ddet_le_Adet
  simp [hD]

end Matrix
