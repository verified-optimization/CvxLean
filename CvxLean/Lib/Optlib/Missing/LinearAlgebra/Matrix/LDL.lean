import Mathlib.LinearAlgebra.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block

import CvxLean.Lib.Optlib.Missing.LinearAlgebra.Matrix.Spectrum
import CvxLean.Lib.Optlib.Missing.Analysis.InnerProductSpace.GramSchmidtOrtho
import CvxLean.Lib.Optlib.Missing.LinearAlgebra.Matrix.Triangular

variable {𝕜 : Type _} 
variable [IsROrC 𝕜]
variable {n : Type _} [LinearOrder n] [IsWellOrder n (· < · : n → n → Prop)] [LocallyFiniteOrderBot n]

open Matrix

open scoped Matrix ComplexOrder

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

@[simp] 
lemma LDL.lowerInv_diagonal (i : n) :
  LDL.lowerInv hS i i = 1 := by
  rw [LDL.lowerInv_eq_gramSchmidtBasis]
  simpa only [gramSchmidtBasis, Basis.coe_mk]
    using @repr_gramSchmidt_diagonal 𝕜 (n → 𝕜) _ (NormedAddCommGroup.ofMatrix hS.transpose)
      (InnerProductSpace.ofMatrix hS.transpose) n _ _ _ i (Pi.basisFun 𝕜 n)

lemma LDL.lower_eq_to_matrix : LDL.lower hS = ((@gramSchmidtBasis 𝕜 (n → 𝕜) _
  (NormedAddCommGroup.ofMatrix hS.transpose) (InnerProductSpace.ofMatrix hS.transpose) 
  n _ _ _ (Pi.basisFun 𝕜 n)).toMatrix (Pi.basisFun 𝕜 n))ᵀ := by
  simp only [LDL.lower, LDL.lowerInv_eq_gramSchmidtBasis]
  apply Matrix.inv_eq_left_inv
  rw [←transpose_mul, Basis.toMatrix_mul_toMatrix_flip, transpose_one]

lemma LDL.lowerTriangular_lowerInv : lowerTriangular (LDL.lowerInv hS) := by 
  apply LDL.lowerInv_triangular

lemma LDL.lowerTriangular_lower : lowerTriangular (LDL.lower hS) :=
  lowerTriangular_inv_of_lowerTriangular (LDL.lowerTriangular_lowerInv hS)

noncomputable instance LDL.invertible_lower : Invertible (LDL.lower hS) :=
  invertibleOfLeftInverse _ _ (Matrix.mul_inv_of_invertible (LDL.lowerInv hS))

@[simp] 
lemma inv_lower_eq_lowerInv : (LDL.lower hS)⁻¹ = LDL.lowerInv hS :=
  Matrix.inv_eq_left_inv (Matrix.mul_inv_of_invertible (LDL.lowerInv hS))

@[simp] 
lemma LDL.lower_diagonal (i : n) :
  LDL.lower hS i i = 1 := by 
  simpa using diag_inv_mul_diag_eq_one_of_lowerTriangular (LDL.lowerTriangular_lower hS) i

@[simp] 
lemma LDL.det_lowerInv :
  (LDL.lowerInv hS).det = 1 := by
  rw [det_of_lowerTriangular (LDL.lowerInv hS) (by apply LDL.lowerInv_triangular),
    Finset.prod_eq_one]
  intros
  rw [LDL.lowerInv_diagonal]

@[simp] 
lemma LDL.det_lower :
  (LDL.lower hS).det = 1 :=
by simp [LDL.lower]
