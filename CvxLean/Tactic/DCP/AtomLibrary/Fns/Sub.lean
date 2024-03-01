import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom sub [affine] (x : ℝ)+ (y : ℝ)- : x - y :=
bconditions
homogenity by
  change _ * _ + _ = _ * _ - _ * _ + _ * _
  ring
additivity by
  ring
optimality by
  intros x' y' hx hy
  apply sub_le_sub hx hy

declare_atom Vec.sub [affine] (m : Nat)& (x : Fin m → ℝ)+ (y : Fin m → ℝ)- : x - y :=
bconditions
homogenity by
  simp [smul_sub]
additivity by
  ring
optimality by
  intros x' y' hx hy i
  exact sub_le_sub (hx i) (hy i)

declare_atom Matrix.sub [affine] (m : Type)& (n : Type)&
  (A : Matrix.{0,0,0} m n ℝ)+ (B : Matrix.{0,0,0} m n ℝ)- : A - B :=
bconditions
homogenity by
  funext i j
  simp [mul_sub]
additivity by
  rw [sub_self, add_zero, sub_add_sub_comm]
optimality by
  intros A' B' hA hB i j
  exact sub_le_sub (hA i j) (hB i j)

end CvxLean
