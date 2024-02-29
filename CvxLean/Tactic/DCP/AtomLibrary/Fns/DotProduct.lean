import CvxLean.Tactic.DCP.AtomCmd

namespace CvxLean

declare_atom Vec.dotProduct1 [affine] (m : Nat)& (x : Fin m → ℝ)& (y : Fin m → ℝ)? : Matrix.dotProduct x y :=
bconditions
homogenity by
  rw [Matrix.dotProduct_zero, smul_zero, add_zero, add_zero,
      Matrix.dotProduct_smul]
additivity by
  rw [Matrix.dotProduct_zero, add_zero, Matrix.dotProduct_add]
optimality le_refl _

declare_atom Vec.dotProduct2 [affine] (m : Nat)& (x : Fin m → ℝ)? (y : Fin m → ℝ)& : Matrix.dotProduct x y :=
bconditions
homogenity by
  rw [Matrix.zero_dotProduct, smul_zero, add_zero, add_zero,
      Matrix.smul_dotProduct]
additivity by
  rw [Matrix.zero_dotProduct, add_zero, Matrix.add_dotProduct]
optimality le_refl _

end CvxLean
