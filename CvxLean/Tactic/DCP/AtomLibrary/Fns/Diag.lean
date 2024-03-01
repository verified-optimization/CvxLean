import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom Matrix.diag [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ : A.diag :=
bconditions
homogenity by
  rw [Matrix.diag_zero, add_zero, smul_zero, add_zero]
  rfl
additivity by
  rw [Matrix.diag_zero, add_zero]
  rfl
optimality fun _ h i => h i i

end CvxLean
