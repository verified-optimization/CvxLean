import CvxLean.Tactic.DCP.Atoms

namespace CvxLean

-- TODO: make argument increasing, without breaking det-log-atom
declare_atom Matrix.diag [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)? : A.diag :=
bconditions
homogenity by
  rw [Matrix.diag_zero, add_zero, smul_zero, add_zero]
  rfl
additivity by
  rw [Matrix.diag_zero, add_zero]
  rfl
optimality le_refl _

end CvxLean
