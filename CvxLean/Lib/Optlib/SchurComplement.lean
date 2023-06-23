/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Jeremy Avigad, Johan Commelin
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.Pi

/-! # Schur complement
This file proves properties of the Schur complement `D - C A⁻¹ B` of a block Matrix `[A B; C D]`.
abentkamp marked this conversation as resolved.
Show resolved
The determinant of a block Matrix in terms of the Schur complement is expressed in the lemmas
`Matrix.det_fromBlocks₁₁` and `Matrix.det_fromBlocks₂₂` in the file
`LinearAlgebra.Matrix.NonsingularInverse`.
## Main result
 * `Matrix.posSemidef.fromBlocks₁₁` : If a Matrix `A` is positive definite, then 
 `[A B; Bᴴ D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.
-/

namespace Matrix

variable {n : Type _} {m : Type _} {𝕜 : Type _} [IsROrC 𝕜]

scoped infix:65 " ⊕ᵥ " => Sum.elim 

lemma schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n]
  {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜)
  [Invertible A] (hA : A.IsHermitian) :
vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vecMul (star (x + (A⁻¹ ⬝ B).mulVec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mulVec y) +
    vecMul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y := by
  simp [Function.star_sum_elim, fromBlocks_mulVec, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, vecMul_mulVec, hA.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

lemma schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n]
  (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜)
  [Invertible D] (hD : D.IsHermitian) :
vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vecMul (star ((D⁻¹ ⬝ Bᴴ).mulVec x + y)) D ⬝ᵥ ((D⁻¹ ⬝ Bᴴ).mulVec x + y) +
    vecMul (star x) (A - B ⬝ D⁻¹ ⬝ Bᴴ) ⬝ᵥ x := by
  simp [Function.star_sum_elim, fromBlocks_mulVec, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, vecMul_mulVec, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

lemma IsHermitian.fromBlocks₁₁ [Fintype m] [DecidableEq m]
  {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜)
  (hA : A.IsHermitian) :
  (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian := by
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian
  { apply isHermitian_conjTranspose_mul_mul
    apply hA.inv }
  rw [isHermitian_fromBlocks_iff]
  constructor
  { intro h
    apply IsHermitian.sub h.2.2.2 hBAB }
  { intro h
    refine' ⟨hA, rfl, conjTranspose_conjTranspose B, _⟩
    rw [← sub_add_cancel D]
    apply IsHermitian.add h hBAB }

lemma IsHermitian.fromBlocks₂₂ [Fintype n] [DecidableEq n]
  (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) {D : Matrix n n 𝕜}
  (hD : D.IsHermitian) :
  (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).IsHermitian := by
  rw [←isHermitian_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert IsHermitian.fromBlocks₁₁ _ _ hD <;> rw [conjTranspose_conjTranspose]

lemma PosSemidef.fromBlocks₁₁ [Fintype m] [DecidableEq m] [Fintype n]
  {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜)
  (hA : A.PosDef) [Invertible A] :
  (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).PosSemidef := by
  rw [PosSemidef, IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  { -- NOTE(RFM): refine λ h, ⟨h.1, λ x, _⟩,
    intro h; refine' ⟨h.1, _⟩; intro x 
    have := h.2 (- ((A⁻¹ ⬝ B).mulVec x) ⊕ᵥ x)
    rw [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self,
      dotProduct_zero, zero_add] at this
    rw [dotProduct_mulVec]; exact this }
  { -- NOTE(RFM): refine λ h, ⟨h.1, λ x, _⟩,
    intro h; refine' ⟨h.1, _⟩; intro x 
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1,
      map_add]
    apply le_add_of_nonneg_of_le
    { rw [← dotProduct_mulVec]
      apply hA.posSemidef.2 }
    { rw [← dotProduct_mulVec _ _ (x ∘ Sum.inr)] 
      apply h.2 } }

lemma PosSemidef.fromBlocks₂₂ [Fintype m] [Fintype n] [DecidableEq n]
  (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) {D : Matrix n n 𝕜}
  (hD : D.PosDef) [Invertible D] :
  (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).PosSemidef := by
  rw [←posSemidef_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert @PosSemidef.fromBlocks₁₁ m n 𝕜 _ _ _ _ _ _ _ hD _ <;>
  rw [conjTranspose_conjTranspose]

end Matrix 
