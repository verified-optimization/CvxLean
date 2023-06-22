import Mathlib.LinearAlgebra.Matrix.Spectrum

import CvxLean.Lib.Optlib.Missing.Analysis.InnerProductSpace.Spectrum

namespace Matrix

variable {𝕜 : Type _} [IsROrC 𝕜] [DecidableEq 𝕜] {n : Type _} [Fintype n] [DecidableEq n]

variable {A : Matrix n n 𝕜}

open Matrix

open BigOperators

-- NOTE(RFM): I needed to change the notion of add comm group for n → 𝕜.
@[local instance]
noncomputable def frobeniusNormedAddCommGroup' [NormedAddCommGroup 𝕜] : NormedAddCommGroup (n → 𝕜) :=
  (by infer_instance : NormedAddCommGroup (PiLp 2 fun j : n => 𝕜))

attribute [-instance] Pi.normedAddCommGroup

noncomputable instance : InnerProductSpace 𝕜 (n → 𝕜) :=
  @PiLp.innerProductSpace 𝕜 _ n _ (fun _ => 𝕜) _ _

lemma IsHermitian.hasEigenvector_eigenvectorBasis (hA : A.IsHermitian) (i : n) :
  Module.End.HasEigenvector (Matrix.toLin' A) (hA.eigenvalues i) (hA.eigenvectorBasis i) := by
  simp only [IsHermitian.eigenvectorBasis, OrthonormalBasis.coe_reindex]
  apply LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis 

end Matrix
