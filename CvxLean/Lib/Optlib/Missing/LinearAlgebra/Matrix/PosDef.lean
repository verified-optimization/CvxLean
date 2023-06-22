import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] {m n : Type _} [Fintype m] [Fintype n]

lemma PosSemidef.eigenvalues_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) [DecidableEq n] (i : n) : 0 ≤ hM.1.eigenvalues i :=
by rw [hM.1.eigenvalues_eq]; apply hM.2

lemma PosDef.eigenvalues_pos {M : Matrix n n ℝ} (hM : M.PosDef) [DecidableEq n] (i : n) : 0 < hM.1.eigenvalues i := by
  rw [hM.1.eigenvalues_eq]
  apply hM.2 _
  intros h
  have h_det : (hM.1.eigenvectorMatrix)ᵀ.det = 0 :=  
    Matrix.det_eq_zero_of_row_eq_zero i (fun j => congr_fun h j)
  simpa only [h_det, not_isUnit_zero] using
    isUnit_det_of_invertible hM.1.eigenvectorMatrixᵀ

lemma PosSemidef_diagonal [DecidableEq n] {f : n → ℝ} (hf : ∀ i, 0 ≤ f i) :
  (diagonal f).PosSemidef := by
  refine' ⟨isHermitian_diagonal _, _⟩
  intro x
  simp only [star, id.def, IsROrC.re_to_real]
  apply Finset.sum_nonneg'
  intro i
  rw [mulVec_diagonal f x i, mul_comm, mul_assoc]
  exact mul_nonneg (hf i) (mul_self_nonneg (x i))

lemma PosDef_diagonal [DecidableEq n] {f : n → ℝ} (hf : ∀ i, 0 < f i) :
  (diagonal f).PosDef := by
  refine' ⟨isHermitian_diagonal _, _⟩
  intros x hx
  simp only [star, id.def, IsROrC.re_to_real]
  apply Finset.sum_pos'
  { intros i _
    rw [mulVec_diagonal f x i, mul_comm, mul_assoc]
    exact mul_nonneg (le_of_lt (hf i)) (mul_self_nonneg (x i)) }
  { contrapose hx; simp at hx ⊢ 
    ext i
    have := hx i
    rw [mulVec_diagonal f x i, mul_comm, mul_assoc] at this
    have := nonpos_of_mul_nonpos_right this (hf i)
    rw [mul_self_eq_zero.1 (le_antisymm this (mul_self_nonneg (x i)))]
    rfl }

lemma PosSemidef.conjTranspose_mul_mul (M N : Matrix n n 𝕜) (hM : M.PosSemidef) :
  (Nᴴ ⬝ M ⬝ N).PosSemidef := by
  refine' ⟨isHermitian_conjTranspose_mul_mul _ hM.1, _⟩
  intro x
  convert hM.2 (N.mulVec x) using 2
  rw [Matrix.mul_assoc, mulVec_mulVec, ←mulVec_mulVec, dotProduct_mulVec, star_mulVec]

lemma PosDef.conjTranspose_mul_mul [DecidableEq n]
    (M N : Matrix n n 𝕜) (hM : M.PosDef) (hN : N.det ≠ 0):
  (Nᴴ ⬝ M ⬝ N).PosDef := by
  refine' ⟨isHermitian_conjTranspose_mul_mul _ hM.1, _⟩
  intros x hx
  convert hM.2 (N.mulVec x) (fun h => hx (eq_zero_of_mulVec_eq_zero hN h)) using 2
  rw [Matrix.mul_assoc, mulVec_mulVec, ←mulVec_mulVec, dotProduct_mulVec, star_mulVec]

end Matrix 
