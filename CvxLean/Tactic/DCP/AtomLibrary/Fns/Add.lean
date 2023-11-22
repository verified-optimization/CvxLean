import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom add [affine] (x : ℝ)+ (y : ℝ)+ : x + y :=
bconditions
homogenity by
  simp [mul_add]
additivity by
  simp only [add_zero, add_assoc, add_comm]
  rw [add_comm x' y', ←add_assoc y y' x', add_comm _ x']
optimality fun _ _ => add_le_add

declare_atom Vec.add [affine] (m : Nat)&  (x : Fin m → ℝ)+ (y : Fin m → ℝ)+ : x + y :=
bconditions
homogenity by
  simp [smul_add]
additivity by
  ring
optimality by
  intros x' y' hx hy i
  apply add_le_add (hx i) (hy i)

declare_atom Matrix.add [affine] (m : Type)& (n : Type)&
(A : Matrix.{0,0,0} m n ℝ)+ (B : Matrix.{0,0,0} m n ℝ)+ : A + B :=
bconditions
homogenity by
  rw [add_zero, add_zero, smul_zero, add_zero, smul_add]
additivity by
  rw [add_zero, add_zero, add_assoc, add_comm B, add_assoc A', add_comm B']
  simp only [add_assoc]
optimality by
  intros A' B' hA hB i j
  apply add_le_add (hA i j) (hB i j)

end CvxLean
