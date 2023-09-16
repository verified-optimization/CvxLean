import Mathlib.LinearAlgebra.Matrix.Spectrum

import CvxLean.Lib.Optlib.Missing.Analysis.InnerProductSpace.Spectrum

namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {n : Type _} [Fintype n] [DecidableEq n]

variable {A : Matrix n n 𝕜}

open Matrix

open BigOperators

-- NOTE: I need to change the instance of normed add comm group for n → 𝕜
-- so that it picks the correct inner product space instance.
@[local instance]
noncomputable def frobeniusNormedAddCommGroup' [NormedAddCommGroup 𝕜] : NormedAddCommGroup (n → 𝕜) :=
  (by infer_instance : NormedAddCommGroup (PiLp 2 fun j : n => 𝕜))

attribute [-instance] Pi.normedAddCommGroup

noncomputable instance : InnerProductSpace 𝕜 (n → 𝕜) :=
  EuclideanSpace.instInnerProductSpace

lemma IsHermitian.hasEigenvector_eigenvectorBasis (hA : A.IsHermitian) (i : n) :
  Module.End.HasEigenvector (Matrix.toLin' A) (hA.eigenvalues i) (hA.eigenvectorBasis i) := by
  simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.coe_reindex]
  apply LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis 

-- TODO: can be used to prove `spectral_theorem`.
/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis using a matrix consisting of eigenvectors. -/
theorem spectral_theorem (xs : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (as : n → ℝ)
    (hxs : ∀ j, Module.End.HasEigenvector (Matrix.toLin' A) (as j) (xs j)) :
  xs.toBasis.toMatrix (Pi.basisFun 𝕜 n) * A =
    diagonal (IsROrC.ofReal ∘ as) * xs.toBasis.toMatrix (Pi.basisFun 𝕜 n) := by
  rw [basis_toMatrix_basisFun_mul]
  ext i j
  let xs' := xs.reindex (Fintype.equivOfCardEq (Fintype.card_fin _)).symm 
  let as' : Fin (Fintype.card n) → ℝ := fun i => as $ (Fintype.equivOfCardEq (Fintype.card_fin _)) i
  have hxs' : ∀ j, Module.End.HasEigenvector (Matrix.toLin' A) (as' j) (xs' j) := by
    simp only [OrthonormalBasis.coe_reindex, Equiv.symm_symm]
    intros j 
    exact (hxs ((Fintype.equivOfCardEq (Fintype.card_fin _)) j))
  convert @LinearMap.spectral_theorem' 𝕜 _ 
    (PiLp 2 (fun (_ : n) => 𝕜)) _ _ (Fintype.card n) (Matrix.toLin' A)
    (EuclideanSpace.single j 1)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
    xs' as' hxs'
  { erw [toLin'_apply]
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, of_apply, OrthonormalBasis.repr_reindex]
    erw [Equiv.symm_apply_apply, EuclideanSpace.single, PiLp.equiv_symm_apply 2, mulVec_single]
    simp_rw [mul_one]
    rfl }
  { simp only [diagonal_mul, Function.comp]
    erw [Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_reindex,
      Pi.basisFun_apply, LinearMap.coe_stdBasis,
      EuclideanSpace.single, PiLp.equiv_symm_apply 2, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
    rfl }

lemma det_eq_prod_eigenvalues (xs : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (as : n → ℝ)
    (hxs : ∀ j, Module.End.HasEigenvector (Matrix.toLin' A) (as j) (xs j)) :
  det A = ∏ i, as i := by
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse
    (Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun 𝕜 n) xs.toBasis))
  rw [←det_mul, spectral_theorem xs as hxs, det_mul, mul_comm, det_diagonal]
  simp

end Matrix
