import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

open Matrix

declare_atom Matrix.diagonal [affine] (n : ℕ)& (d : Fin n → ℝ)+ : diagonal d :=
bconditions
homogenity by
  erw [diagonal_zero, add_zero, smul_zero, add_zero, diagonal_smul]
additivity by
  erw [Matrix.diagonal_add, diagonal_zero, add_zero]
  rfl
optimality by
  intros d' hd i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h, hd j]

end CvxLean
