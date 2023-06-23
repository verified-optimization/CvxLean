import linear_algebra.matrix.ldl
import linear_algebra.matrix.block

import missing.analysis.inner_product_space.gram_schmidt_ortho
import missing.linear_algebra.matrix.triangular

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {n : Type*} [linear_order n] [is_well_order n (<)] [locally_finite_order_bot n]

local notation `⟪`x`, `y`⟫` :=
@inner 𝕜 (n → 𝕜) (pi_Lp.inner_product_space (λ _, 𝕜)).to_has_inner x y

open matrix
open_locale matrix

variables {S : matrix n n 𝕜} [fintype n] (hS : S.pos_def)

@[simp] lemma LDL.lower_inv_diagonal (i : n) :
  LDL.lower_inv hS i i = 1 :=
begin
  rw [LDL.lower_inv_eq_gram_schmidt_basis, basis.to_matrix],
  simpa only [gram_schmidt_basis, basis.coe_mk]
    using @repr_gram_schmidt_diagonal 𝕜 (n → 𝕜) _
      (inner_product_space.of_matrix hS.transpose) n _ _ _ i (pi.basis_fun 𝕜 n)
end

lemma LDL.lower_eq_to_matrix : LDL.lower hS = ((@gram_schmidt_basis 𝕜 (n → 𝕜) _
  (inner_product_space.of_matrix hS.transpose) n _ _ _ (pi.basis_fun 𝕜 n)).to_matrix
    (pi.basis_fun 𝕜 n))ᵀ :=
begin
  simp only [LDL.lower, LDL.lower_inv_eq_gram_schmidt_basis],
  apply matrix.inv_eq_left_inv,
  rw [←transpose_mul, basis.to_matrix_mul_to_matrix_flip, transpose_one]
end

lemma LDL.lower_triangular_lower_inv : lower_triangular (LDL.lower_inv hS) :=
by apply LDL.lower_inv_triangular

lemma LDL.lower_triangular_lower : lower_triangular (LDL.lower hS) :=
lower_triangular_inv_of_lower_triangular (LDL.lower_triangular_lower_inv hS)

noncomputable instance LDL.invertible_lower : invertible (LDL.lower hS) :=
invertible_of_left_inverse _ _ (matrix.mul_inv_of_invertible (LDL.lower_inv hS))

@[simp] lemma inv_lower_eq_lower_inv : (LDL.lower hS)⁻¹ = LDL.lower_inv hS :=
matrix.inv_eq_left_inv (matrix.mul_inv_of_invertible (LDL.lower_inv hS))

@[simp] lemma LDL.lower_diagonal (i : n) :
  LDL.lower hS i i = 1 :=
by simpa using diag_inv_mul_diag_eq_one_of_lower_triangular (LDL.lower_triangular_lower hS) i

@[simp] lemma LDL.det_lower_inv :
  (LDL.lower_inv hS).det = 1 :=
begin
  rw [det_of_lower_triangular (LDL.lower_inv hS) (by apply LDL.lower_inv_triangular),
    finset.prod_eq_one],
  intros,
  rw LDL.lower_inv_diagonal,
end

@[simp] lemma LDL.det_lower :
  (LDL.lower hS).det = 1 :=
by simp [LDL.lower]
