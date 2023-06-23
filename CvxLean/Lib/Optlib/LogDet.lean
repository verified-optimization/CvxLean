import Mathlib.LinearAlgebra.Matrix.LDL

import CvxLean.Lib.Optlib.SchurComplement
import CvxLean.Lib.Optlib.Subadditivity

import CvxLean.Lib.Optlib.Missing.LinearAlgebra.Matrix.Triangular

/- In this file we prove properties needed for the log-det-atom.
We follow the proof in the Mosek documentation:
https://docs.mosek.com/modeling-cookbook/sdo.html#log-determinant -/

namespace Matrix

open Matrix
open BigOperators

variable {n : Type} [Fintype n] [LinearOrder n] [LocallyFiniteOrderBot n]
variable {𝕜 : Type} [IsROrC 𝕜]
variable {A : Matrix n n ℝ} (hA : A.PosDef)

noncomputable instance LDL.invertible_diag : Invertible (LDL.diag hA) := by
  rw [LDL.diag_eq_lowerInv_conj]
  refine @invertibleMul _ _ _ _ (@invertibleMul _ _ _ _ _ hA.Invertible) _

@[simp] 
lemma PosSemidef_zero : PosSemidef (0 : Matrix n n 𝕜) :=
by simp [PosSemidef]

lemma LogDetAtom.feasibility_PosDef {D Z : Matrix n n ℝ}
  (hD : D = LDL.diag hA)
  (hZ : Z = LDL.diag hA ⬝ (LDL.lower hA)ᵀ) :
  (fromBlocks D Z Zᵀ A).PosSemidef := by
  have h_D_eq : D = Z ⬝ A⁻¹ ⬝ Zᴴ := 
    calc D 
      = D ⬝ D⁻¹ ⬝ D := by 
          rw [hD, Matrix.mul_inv_of_invertible, Matrix.one_mul]
    _ = D ⬝ (LDL.lowerInv hA ⬝ A ⬝ (LDL.lowerInv hA)ᵀ)⁻¹ ⬝ Dᵀ := by 
          erw [hD, LDL.diag, diagonal_transpose, ← LDL.diag, LDL.diag_eq_lowerInv_conj]
          rfl
    _ = D ⬝ (LDL.lower hA)ᵀ ⬝ A⁻¹ ⬝ (D ⬝ (LDL.lower hA)ᵀ)ᵀ := by 
          simp only [hD, LDL.lower, transpose_mul, transpose_transpose, transpose_nonsing_inv,
            Matrix.mul_assoc, Matrix.mul_inv_rev]
    _ = Z ⬝ A⁻¹ ⬝ Zᴴ := by 
          rw [hZ, hD]; rfl
  haveI := hA.Invertible
  erw [PosSemidef.fromBlocks₂₂ _ _ hA]
  simp [h_D_eq]

def toUpperTri {m α : Type _} [LinearOrder m] [Zero α] (A : Matrix m m α) : Matrix m m α :=
  fun i j => if i ≤ j then A i j else 0

lemma upperTriangular_toUpperTri (A : Matrix n n ℝ) : A.toUpperTri.upperTriangular := by
  intros i j hij
  unfold toUpperTri
  rw [if_neg]
  simpa using hij

lemma upperTriangular.toUpperTri_eq {A : Matrix n n ℝ} (hA : upperTriangular A) :
  A.toUpperTri = A := by
  ext i j
  by_cases i ≤ j
  simp [toUpperTri, h]
  simp [toUpperTri, h, hA (lt_of_not_ge h)]

lemma LogDetAtom.feasibility_PosDef' {D Z Y : Matrix n n ℝ}
  (hY : Y = LDL.diag hA ⬝ (LDL.lower hA)ᵀ)
  (hD : D = diagonal Y.diag)
  (hZ : Z = Y.toUpperTri) :
  (fromBlocks D Z Zᵀ A).PosSemidef := by
  have hY_tri : upperTriangular Y
  { rw [hY]
    apply upperTriangular.mul
    apply BlockTriangular_diagonal
    apply lowerTriangular.transpose
    apply LDL.lowerTriangular_lower }
  haveI := hA.invertible,
  rw [hZ, hY_tri.toUpperTri_eq],
  apply log_det_atom.feasibility_pos_def _ _ hY,
  simp [hD, hY, LDL.diag],
end

lemma LDL.diag_entries_pos {A : matrix n n ℝ} (hA: A.pos_def) (i : n) :
  0 < LDL.diag_entries hA i :=
begin
  have : (LDL.lower_inv hA).det ≠ 0, by simp [LDL.det_lower_inv hA],
  have : LDL.lower_inv hA i ≠ 0,
    from λ h, this (matrix.det_eq_zero_of_row_eq_zero i (λ j, congr_fun h j)),
  exact hA.2 (LDL.lower_inv hA i) this,
end

lemma log_det_atom.solution_eq_atom {A : matrix n n ℝ} (hA: A.pos_def) :
  (∑ i, real.log (LDL.diag_entries hA i)) = real.log (A.det) :=
begin
  conv { to_rhs, rw [(LDL.lower_conj_diag hA).symm] },
  have := real.log_prod finset.univ (LDL.diag_entries hA)
    (λ i _, ne_of_gt (LDL.diag_entries_pos hA i)),
  simp [LDL.diag, this.symm]
end

lemma log_det_atom.feasibility_exp {A : matrix n n ℝ} (hA: A.pos_def) (i : n) :
  LDL.diag_entries hA i ≤ ((LDL.diag hA) ⬝ ((LDL.lower hA)ᵀ)).diag i :=
by simp [LDL.diag]

lemma IsHermitian₁₁_of_IsHermitian_toBlock
  {A B C D : matrix n n ℝ} (h : (fromBlocks A B C D).IsHermitian) :
  IsHermitian A :=
by { ext i j, simpa using congr_fun (congr_fun h (sum.inl i)) (sum.inl j) }

lemma IsHermitian₂₂_of_IsHermitian_toBlock
  {A B C D : matrix n n ℝ} (h : (fromBlocks A B C D).IsHermitian) :
  IsHermitian D :=
by { ext i j, simpa using congr_fun (congr_fun h (sum.inr i)) (sum.inr j) }

lemma PosSemidef₁₁_of_PosSemidef_toBlock
  {A B C D : matrix n n ℝ}
  (h_posdef : (fromBlocks A B C D).PosSemidef) :
  PosSemidef A :=
⟨IsHermitian₁₁_of_IsHermitian_toBlock h_posdef.1,
  λ x, by simpa [matrix.fromBlocks_mul_vec, star] using h_posdef.2 (sum.elim x 0)⟩

lemma PosSemidef₂₂_of_PosSemidef_toBlock
  {A B C D : matrix n n ℝ}
  (h_posdef : (fromBlocks A B C D).PosSemidef) :
  PosSemidef D :=
⟨IsHermitian₂₂_of_IsHermitian_toBlock h_posdef.1,
  λ x, by simpa [matrix.fromBlocks_mul_vec, star] using h_posdef.2 (sum.elim 0 x)⟩

lemma log_det_atom.optimality_D_posdef {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
  (h_posdef : (fromBlocks D Z Zᵀ A).PosSemidef) :
  D.pos_def :=
begin
  have h_D_psd : D.PosSemidef := PosSemidef₁₁_of_PosSemidef_toBlock h_posdef,
  show D.pos_def,
  { rw [h_D_psd.pos_def_iff_det_ne_zero, hD, det_diagonal, finset.prod_ne_zero_iff],
    exact λ i _, ne_of_gt (lt_of_lt_of_le ((t i).exp_pos) (ht i)) },
end

lemma log_det_atom.optimality_Ddet_le_Adet {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
  (h_posdef : (fromBlocks D Z Zᵀ A).PosSemidef) :
  D.det ≤ A.det :=
begin
  by_cases h_nonempty : nonempty n,
  { have h_D_pd : D.pos_def, from log_det_atom.optimality_D_posdef ht hD hZ h_posdef,
    haveI h_D_invertible : invertible D := h_D_pd.invertible,
    have h_Zdet : Z.det = D.det,
    { rw [hZ, det_of_upperTriangular (upperTriangular_toUpperTri Y), hD, det_diagonal],
      simp [toUpperTri], },
    have h_ZDZ_semidef : (Zᴴ ⬝ D⁻¹ ⬝ Z).PosSemidef,
    from PosSemidef.conj_transpose_mul_mul D⁻¹ Z h_D_pd.nonsingular_inv.PosSemidef,
    have h_AZDZ_semidef : (A - Zᴴ ⬝ D⁻¹ ⬝ Z).PosSemidef,
      from (PosSemidef.fromBlocks₁₁ Z A h_D_pd).1 h_posdef,
    show D.det ≤ A.det,
    { apply le_of_add_le_of_nonneg_left _ h_AZDZ_semidef.det_nonneg,
      simpa [h_Zdet] using det_add_det_le_det_add _ _ h_ZDZ_semidef h_AZDZ_semidef } },
  { haveI h_empty := not_nonempty_iff.1 h_nonempty,
    simp only [matrix.det_is_empty] }
end

lemma log_det_atom.cond_elim {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
  (h_posdef : (fromBlocks D Z Zᵀ A).PosSemidef) :
  A.pos_def :=
begin
  have h_D_pd : D.pos_def, from log_det_atom.optimality_D_posdef ht hD hZ h_posdef,
  have h_A_psd : A.PosSemidef := PosSemidef₂₂_of_PosSemidef_toBlock h_posdef,
  have h_Ddet_le_Adet : D.det ≤ A.det := log_det_atom.optimality_Ddet_le_Adet ht hD hZ h_posdef,
  have h_Adet_pos : 0 < A.det, from lt_of_lt_of_le h_D_pd.det_pos h_Ddet_le_Adet,
  rw h_A_psd.pos_def_iff_det_ne_zero,
  apply ne_of_gt h_Adet_pos
end

lemma log_det_atom.optimality {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.toUpperTri)
  (h_posdef : (fromBlocks D Z Zᵀ A).PosSemidef) :
  ∑ i, t i ≤ real.log A.det :=
begin
  have h_A_pd : A.pos_def, from log_det_atom.cond_elim ht hD hZ h_posdef,
  have h_Ddet_le_Adet : D.det ≤ A.det := log_det_atom.optimality_Ddet_le_Adet ht hD hZ h_posdef,
  have h_Adet_pos: 0 < A.det, from h_A_pd.det_pos,
  rw [←real.exp_le_exp, real.exp_sum, real.exp_log h_Adet_pos],
  apply le_trans (finset.prod_le_prod (λ i _, le_of_lt ((t i).exp_pos)) (λ i _, ht i)),
  convert h_Ddet_le_Adet,
  simp [hD]
end



end matrix
