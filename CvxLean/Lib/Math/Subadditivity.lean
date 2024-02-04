import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.DotProduct
import CvxLean.Lib.Math.LinearAlgebra.Matrix.PosDef
import CvxLean.Lib.Math.LinearAlgebra.Matrix.Spectrum
import CvxLean.Lib.Math.LinearAlgebra.Eigenspace

namespace Finset

open BigOperators

lemma one_add_prod_le_prod_one_add {n : Type _} [Fintype n] [Nonempty n]
  (f : n → ℝ) (hf : ∀ i, 0 ≤ f i) : 1 + (∏ i, f i) ≤ ∏ i, (1 + f i) := by
  classical
  calc 1 + (∏ i, f i)
    = (∏ _a : n, 1 : ℝ) * ∏ a : n in univ \ univ, f a
      + (∏ a : n in ∅, 1) * ∏ a : n in univ \ ∅, f a := by
    { simp }
  _ = ∑ x in {univ, ∅}, (∏ _a : n in x, 1 : ℝ) * ∏ a : n in univ \ x, f a := by
    { rw [Finset.sum_pair]; simp; exact Finset.univ_nonempty.ne_empty }
  _ ≤ ∑ t : Finset n, (∏ _a : n in t, 1 : ℝ) * ∏ a : n in univ \ t, f a := by
    { convert @Finset.sum_le_univ_sum_of_nonneg (Finset n) ℝ _ _ _ _ _
      simp [hf, prod_nonneg] }
  _ = ∏ i, (1 + f i) := by
    { rw [prod_add, powerset_univ] }

end Finset

namespace Matrix

variable {n : Type _} [Fintype n] [DecidableEq n] [LinearOrder n] [LocallyFiniteOrderBot n]

open BigOperators Matrix

namespace IsHermitian

variable {𝕜 : Type _} [DecidableEq 𝕜] [IsROrC 𝕜] {A : Matrix n n 𝕜} (hA : A.IsHermitian)

lemma eigenvectorMatrix_inv_mul :
  hA.eigenvectorMatrixInv * hA.eigenvectorMatrix = 1 :=
by apply Basis.toMatrix_mul_toMatrix_flip

-- NOTE: There is a `spectral_theorem'`.
theorem spectral_theorem'' :
  hA.eigenvectorMatrix * diagonal (IsROrC.ofReal ∘ hA.eigenvalues) * hA.eigenvectorMatrixᴴ = A := by
  rw [conjTranspose_eigenvectorMatrix, Matrix.mul_assoc, ← spectral_theorem,
    ←Matrix.mul_assoc, eigenvectorMatrix_mul_inv, Matrix.one_mul]

end IsHermitian

noncomputable def IsHermitian.sqrt {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
hA.eigenvectorMatrix * Matrix.diagonal (fun i => (hA.eigenvalues i).sqrt) * hA.eigenvectorMatrixᵀ

lemma conjTranspose_eq_transpose {m n : Type _} {A : Matrix m n ℝ} : Aᴴ = Aᵀ := rfl

@[simp]
lemma PosSemidef.sqrt_mul_sqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
  hA.1.sqrt * hA.1.sqrt = A :=
calc
  hA.1.sqrt * hA.1.sqrt =
    hA.1.eigenvectorMatrix * (Matrix.diagonal (fun i => (hA.1.eigenvalues i).sqrt)
    * (hA.1.eigenvectorMatrixᵀ * hA.1.eigenvectorMatrix)
    * Matrix.diagonal (fun i => (hA.1.eigenvalues i).sqrt)) * hA.1.eigenvectorMatrixᵀ := by
    simp [IsHermitian.sqrt, Matrix.mul_assoc]
  _ = A := by
    rw [←conjTranspose_eq_transpose, hA.1.conjTranspose_eigenvectorMatrix,
      hA.1.eigenvectorMatrix_inv_mul, Matrix.mul_one, diagonal_mul_diagonal,
      ← hA.1.conjTranspose_eigenvectorMatrix]
    convert hA.1.spectral_theorem''
    rw [←Real.sqrt_mul (hA.eigenvalues_nonneg _), Real.sqrt_mul_self (hA.eigenvalues_nonneg _)]
    simp

lemma PosSemidef.PosSemidef_sqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
  hA.1.sqrt.PosSemidef :=
PosSemidef.conjTranspose_mul_mul _ _
  (PosSemidef_diagonal (fun i => Real.sqrt_nonneg (hA.1.eigenvalues i)))

lemma IsHermitian.one_add {A : Matrix n n ℝ} (hA : A.IsHermitian) : (1 + A).IsHermitian := by
  dsimp [IsHermitian]; rw [IsHermitian.add _ hA]; simp

lemma IsHermitian.has_eigenvector_one_add {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
  Module.End.HasEigenvector (1 + Matrix.toLin' A) (1 + (hA.eigenvalues i)) ((hA.eigenvectorBasis) i) :=
Module.End.has_eigenvector_add
  (Module.End.has_eigenvector_one (hA.hasEigenvector_eigenvectorBasis i).2)
  (hA.hasEigenvector_eigenvectorBasis i)

lemma PosDef.PosDef_sqrt {A : Matrix n n ℝ} (hA : A.PosDef) :
  hA.1.sqrt.PosDef := by
  unfold IsHermitian.sqrt
  refine'
    PosDef.conjTranspose_mul_mul _ (hA.1.eigenvectorMatrixᵀ)
      (PosDef_diagonal (fun i => Real.sqrt_pos.2 (hA.eigenvalues_pos i))) _
  show det hA.1.eigenvectorMatrixᵀ ≠ 0
  rw [det_transpose]
  apply det_ne_zero_of_right_inverse hA.1.eigenvectorMatrix_mul_inv

lemma PosSemidef.PosDef_iff_det_ne_zero [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosSemidef) :
  M.PosDef ↔ M.det ≠ 0 := by
  refine' ⟨PosDef.det_ne_zero, _⟩; intro hdet; refine' ⟨hM.1, _⟩
  intros x hx
  apply lt_of_le_of_ne' (hM.2 x)
  rw [←hM.sqrt_mul_sqrt, ←mulVec_mulVec, dotProduct_mulVec, ←transpose_transpose hM.1.sqrt,
    vecMul_transpose, transpose_transpose, ← conjTranspose_eq_transpose,
    hM.PosSemidef_sqrt.1.eq]
  simp only [IsROrC.re_to_real, star, id]
  change @inner ℝ (EuclideanSpace ℝ _) _ (hM.1.sqrt.mulVec x) (hM.1.sqrt.mulVec x) ≠ 0
  intro hinner
  have sqrtMdet0 : hM.1.sqrt.det = 0 := by
    refine' exists_mulVec_eq_zero_iff.1 ⟨x, hx, _⟩
    rw [inner_self_eq_zero.1 hinner]
  rw [←hM.sqrt_mul_sqrt, det_mul, sqrtMdet0, mul_zero] at hdet
  apply hdet rfl

/-- Subadditivity lemma for positive semidefinite matrices. This version assumes that one of the
matrices is positive definite. See `det_add_det_le_det_add` for the more general statement.

The argument is taken from Andreas Thom's comment on mathoverflow:
https://mathoverflow.net/questions/65424/determinant-of-sum-of-positive-definite-matrices. -/
lemma det_add_det_le_det_add' [Nonempty n] (A B : Matrix n n ℝ)
    (hA : A.PosDef) (hB : B.PosSemidef) :
  A.det + B.det ≤ (A + B).det := by
  let sqrtA := hA.1.sqrt
  have isUnit_det_sqrtA :=
    isUnit_iff_ne_zero.2 hA.PosDef_sqrt.det_ne_zero
  have : IsUnit sqrtA :=
    (isUnit_iff_isUnit_det _).2 isUnit_det_sqrtA
  have IsHermitian_sqrtA : sqrtA⁻¹.IsHermitian
  { apply IsHermitian.nonsingular_inv (hA.posSemidef.PosSemidef_sqrt.1)
    exact isUnit_det_sqrtA }
  have PosSemidef_ABA : (sqrtA⁻¹ * B * sqrtA⁻¹).PosSemidef :=
    PosSemidef.mul_mul_of_IsHermitian hB IsHermitian_sqrtA
  let μ := PosSemidef_ABA.1.eigenvalues
  calc A.det + B.det
    = A.det * (1 + (sqrtA⁻¹ * B * sqrtA⁻¹).det) := by
        rw [det_mul, det_mul, mul_comm _ B.det, mul_assoc, ←det_mul, ←Matrix.mul_inv_rev,
          hA.posSemidef.sqrt_mul_sqrt, mul_add, mul_one, mul_comm, mul_assoc, ←det_mul,
          nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA.det_ne_zero), det_one, mul_one]
  _ = A.det * (1 + ∏ i, μ i) := by
        rw [PosSemidef_ABA.1.det_eq_prod_eigenvalues]
        rfl
  _ ≤ A.det * ∏ i, (1 + μ i) := by
        apply (mul_le_mul_left hA.det_pos).2
        apply Finset.one_add_prod_le_prod_one_add μ PosSemidef_ABA.eigenvalues_nonneg
  _ = A.det * (1 + sqrtA⁻¹ * B * sqrtA⁻¹).det := by
        rw [mul_eq_mul_left_iff]; left; symm
        rw [det_eq_prod_eigenvalues PosSemidef_ABA.1.eigenvectorBasis
          (fun i => 1 + (PosSemidef_ABA.1.eigenvalues i)) _]
        { simp }
        intro i
        convert PosSemidef_ABA.1.has_eigenvector_one_add i using 1
        simp only [map_add, toLin'_one, toLin'_mul, add_left_inj]
        rfl
  _ = (A + B).det := by
        rw [← det_mul, ← det_conj this (A + B)]
        apply congr_arg
        rw [←hA.posSemidef.sqrt_mul_sqrt]
        change sqrtA * sqrtA * (1 + sqrtA⁻¹ * B * sqrtA⁻¹) = sqrtA * (sqrtA * sqrtA + B) * sqrtA⁻¹
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ _ (B * _),
          Matrix.mul_nonsing_inv _ isUnit_det_sqrtA, Matrix.one_mul, Matrix.mul_one,
          hA.posSemidef.sqrt_mul_sqrt, Matrix.mul_assoc]

/-- Subadditivity lemma for positive semidefinite matrices. -/
lemma det_add_det_le_det_add [Nonempty n] (A B : Matrix n n ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
  A.det + B.det ≤ (A + B).det := by
  by_cases hA' : A.det = 0
  { by_cases hB' : B.det = 0
    { simp [hA', hB']
      apply (hA.add hB).det_nonneg }
    { rw [add_comm A B, add_comm A.det B.det]
      apply det_add_det_le_det_add' _ _ (hB.PosDef_iff_det_ne_zero.2 hB') hA } }
  { apply det_add_det_le_det_add' _ _ (hA.PosDef_iff_det_ne_zero.2 hA') hB }

end Matrix
