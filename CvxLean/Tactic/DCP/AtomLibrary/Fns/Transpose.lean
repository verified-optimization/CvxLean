import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom Matrix.transpose [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ :
  A.transpose :=
bconditions
homogenity by
  simp [Matrix.transpose_zero, smul_zero]
additivity by
  rw [Matrix.transpose_zero, add_zero, Matrix.transpose_add]
optimality by
  intros _ hA i j
  exact hA j i

end CvxLean
