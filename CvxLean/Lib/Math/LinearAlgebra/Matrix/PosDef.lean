import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.Pi

/-!
More results about positive definite and positive semidefinite matrices (see
`Mathlib.LinearAlgebra.Matrix.PosDef`).
-/

namespace Matrix

variable {m n : Type _} [Fintype m] [Fintype n]
variable {𝕜 : Type _}
variable [NormedField 𝕜] [PartialOrder 𝕜] [StarOrderedRing 𝕜]
variable [IsROrC 𝕜]

lemma PosSemidef.det_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef)
    [DecidableEq n] : 0 ≤ det M := by
  rw [hM.1.det_eq_prod_eigenvalues]
  apply Finset.prod_nonneg
  intros i _hi
  apply eigenvalues_nonneg hM

lemma PosDef.det_ne_zero [DecidableEq n] {M : Matrix n n 𝕜} (hM : M.PosDef) :
    M.det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero]
  intros v hv
  have hv' := hv (star v)
  rw [← star_eq_zero]
  by_contra h
  have := hM.2 (star v) h
  simp [star_star, hv'] at this

lemma PosDef.isUnit_det [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    IsUnit M.det :=
  isUnit_iff_ne_zero.2 hM.det_ne_zero

noncomputable instance PosDef.Invertible [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.PosDef) : Invertible M :=
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

lemma PosSemidef.conjTranspose_mul_mul (M N : Matrix n n 𝕜)
    (hM : M.PosSemidef) : (Nᴴ * M * N).PosSemidef := by
  refine' ⟨isHermitian_conjTranspose_mul_mul _ hM.1, _⟩
  intro x
  convert hM.2 (N.mulVec x) using 1
  rw [mul_assoc, mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

lemma PosDef.conjTranspose_mul_mul [DecidableEq n] (M N : Matrix n n 𝕜)
    (hM : M.PosDef) (hN : N.det ≠ 0) : (Nᴴ * M * N).PosDef := by
  refine' ⟨isHermitian_conjTranspose_mul_mul _ hM.1, _⟩
  intros x hx
  convert
    hM.2 (N.mulVec x) (fun h => hx (eq_zero_of_mulVec_eq_zero hN h)) using 1
  rw [Matrix.mul_assoc, mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    star_mulVec]

lemma IsHermitian.nonsingular_inv [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.IsHermitian) (hMdet : IsUnit M.det):
  M⁻¹.IsHermitian := by
  refine' (Matrix.inv_eq_right_inv _).symm
  rw [conjTranspose_nonsing_inv, hM.eq, mul_nonsing_inv _ hMdet]

lemma conj_symm {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    star (star x ⬝ᵥ mulVec M x) = star x ⬝ᵥ mulVec M x := by
  nth_rewrite 1 [star_dotProduct, star_mulVec]
  rw [star_star, dotProduct_mulVec, hM.eq]

lemma PosDef.nonsingular_inv [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.PosDef) : M⁻¹.PosDef := by
  refine' ⟨hM.1.nonsingular_inv (isUnit_iff_ne_zero.2 hM.det_ne_zero), _⟩
  intros x hx
  have hMMinv := mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM.det_ne_zero)
  have hMinvdet : M⁻¹.det ≠ 0 := det_ne_zero_of_left_inverse hMMinv
  have hres :=
    hM.2 (M⁻¹.mulVec x) (fun h => hx (eq_zero_of_mulVec_eq_zero hMinvdet h))
  rw [mulVec_mulVec, hMMinv, one_mulVec, star_dotProduct] at hres
  rw [conj_symm ((@isHermitian_inv _ _ _ _ _ _ M hM.Invertible).2 hM.1)] at hres
  exact hres

lemma PosSemidef.mul_mul_of_IsHermitian {M N : Matrix n n 𝕜}
    (hM : M.PosSemidef) (hN : N.IsHermitian) : (N * M * N).PosSemidef := by
  convert hM.conjTranspose_mul_mul M N; exact hN.symm

lemma PosSemidef.add {M N : Matrix n n 𝕜} (hM : M.PosSemidef)
    (hN : N.PosSemidef) : (M + N).PosSemidef := by
  refine' ⟨hM.1.add hN.1, _⟩
  intros x
  simp only [add_mulVec, dotProduct_add, map_add]
  apply add_nonneg (hM.2 x) (hN.2 x)

lemma isUnit_det_of_PosDef_inv [DecidableEq n] {M : Matrix n n ℝ}
    (h : M⁻¹.PosDef) : IsUnit M.det := by
  apply isUnit_iff_ne_zero.2
  have := h.isUnit_det
  rw [det_nonsing_inv, isUnit_ring_inverse] at this
  apply IsUnit.ne_zero this

lemma PosDef_inv_iff_PosDef [DecidableEq n] (M : Matrix n n ℝ) :
    M⁻¹.PosDef ↔ M.PosDef := by
  constructor
  { intros hM
    rw [← Matrix.nonsing_inv_nonsing_inv M (isUnit_det_of_PosDef_inv hM)]
    apply hM.nonsingular_inv }
  { intros hM
    exact hM.nonsingular_inv }

end Matrix
