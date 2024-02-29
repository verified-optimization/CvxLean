import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Matrix
import CvxLean.Lib.Math.LinearAlgebra.Matrix.ToUpperTri

namespace CvxLean

declare_atom Matrix.toUpperTri [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ :
  Matrix.toUpperTri A :=
bconditions
homogenity by
  rw [Matrix.toUpperTri_zero, add_zero, smul_zero, add_zero,
      Matrix.toUpperTri_smul]
additivity by
  rw [Matrix.toUpperTri_zero, add_zero, Matrix.toUpperTri_add]
optimality by
  intros A' hA i j
  by_cases h : i ≤ j <;> simp [Matrix.toUpperTri, h] ; exact hA i j

end CvxLean
