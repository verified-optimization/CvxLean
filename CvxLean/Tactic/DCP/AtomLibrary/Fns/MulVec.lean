import CvxLean.Tactic.DCP.AtomCmd
namespace CvxLean

declare_atom Matrix.mulVec [affine] (n : ℕ)& (m : ℕ)&
  (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)& (v : Fin n → ℝ)? : Matrix.mulVec M v :=
bconditions
homogenity by
  rw [Matrix.mulVec_zero, smul_zero, add_zero, add_zero, Matrix.mulVec_smul]
additivity by
  simp [Matrix.mulVec_add, Matrix.mulVec_zero, add_zero]
optimality le_refl _

end CvxLean
