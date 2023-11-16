import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom Matrix.mul1 [affine] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)& (B : Matrix.{0,0,0} m m ℝ)? : A * B :=
bconditions
homogenity by
  simp
additivity by
  simp [Matrix.mul_add]
optimality le_refl _

declare_atom Matrix.mul2 [affine] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)? (B : Matrix.{0,0,0} m m ℝ)& : A * B :=
bconditions
homogenity by
  simp
additivity by
  simp [Matrix.add_mul]
optimality le_refl _

end CvxLean
