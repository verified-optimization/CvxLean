import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom Matrix.diagonal [affine] (n : ℕ)& (d : Fin n → ℝ)+ : Matrix.diagonal d :=
bconditions
homogenity by
  rw [Matrix.diagonal_zero', add_zero, smul_zero, add_zero,
      Matrix.diagonal_smul']
additivity by
  rw [Matrix.diagonal_add', Matrix.diagonal_zero', add_zero]
optimality by
  intros d' hd i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h, hd j]

end CvxLean
