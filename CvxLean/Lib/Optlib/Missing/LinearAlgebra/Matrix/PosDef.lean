import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] {m n : Type _} [Fintype m] [Fintype n]

lemma PosSemidef.eigenvalues_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) [DecidableEq n] (i : n) : 0 ≤ hM.1.eigenvalues i :=
by rw [hM.1.eigenvalues_eq]; apply hM.2

lemma PosSemidef.det_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) [DecidableEq n] : 0 ≤ det M := by
  rw [hM.1.det_eq_prod_eigenvalues]
  apply Finset.prod_nonneg
  intros i _hi
  apply eigenvalues_nonneg hM

lemma PosDef.eigenvalues_pos {M : Matrix n n ℝ} (hM : M.PosDef) [DecidableEq n] (i : n) : 0 < hM.1.eigenvalues i := by
  rw [hM.1.eigenvalues_eq]
  apply hM.2 _
  intros h
  have h_det : (hM.1.eigenvectorMatrix)ᵀ.det = 0 :=  
    Matrix.det_eq_zero_of_row_eq_zero i (fun j => congr_fun h j)
  simpa only [h_det, not_isUnit_zero] using
    isUnit_det_of_invertible hM.1.eigenvectorMatrixᵀ

lemma PosDef.det_ne_zero [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) : M.det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  intros v hv
  have hv' := hv (star v)
  rw [← star_eq_zero]
  by_contra h
  have := hM.2 (star v) h
  rw [star_star, hv'] at this
  simp at this

noncomputable instance PosDef.Invertible 
  [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) : Invertible M :=
  invertibleOfIsUnitDet M (isUnit_iff_ne_zero.2 hM.det_ne_zero)

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

lemma IsHermitian.nonsingular_inv [DecidableEq n] {M : Matrix n n 𝕜}
  (hM : M.IsHermitian) (hMdet : IsUnit M.det):
  M⁻¹.IsHermitian := by
  refine' (Matrix.inv_eq_right_inv _).symm
  rw [conjTranspose_nonsing_inv, hM.eq, mul_nonsing_inv _ hMdet]

lemma PosDef.nonsingular_inv [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) :
  M⁻¹.PosDef := by
  refine' ⟨IsHermitian.nonsingular_inv hM.1 (isUnit_iff_ne_zero.2 hM.det_ne_zero), _⟩
  intros x hx
  have hMMinv := (mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM.det_ne_zero))
  have hMinvdet : M⁻¹.det ≠ 0 := det_ne_zero_of_left_inverse hMMinv
  have := hM.2 (M⁻¹.mulVec x) (λ h => hx (eq_zero_of_mulVec_eq_zero hMinvdet h))
  rw [mulVec_mulVec, hMMinv, one_mulVec, star_dotProduct] at this
  rw [← IsROrC.conj_re]
  exact this

lemma PosSemidef.mul_mul_of_IsHermitian {M N : Matrix n n 𝕜}
    (hM : M.PosSemidef) (hN : N.IsHermitian) :
  (N ⬝ M ⬝ N).PosSemidef :=
by convert hM.conjTranspose_mul_mul M N; exact hN.symm

lemma PosSemidef.add {M N : Matrix n n 𝕜} (hM : M.PosSemidef) (hN : N.PosSemidef) :
  (M + N).PosSemidef := by
  refine' ⟨hM.1.add hN.1, _⟩; intros x
  simp only [add_mulVec, dotProduct_add, map_add]
  apply add_nonneg (hM.2 x) (hN.2 x)

end Matrix 
