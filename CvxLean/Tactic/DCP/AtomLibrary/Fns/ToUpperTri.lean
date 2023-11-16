import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Missing.Matrix

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
