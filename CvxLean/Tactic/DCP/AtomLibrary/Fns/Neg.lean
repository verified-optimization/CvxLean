import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Matrix

/-!
Atom for negation (affine).
-/

namespace CvxLean

declare_atom neg [affine] (x : ℝ)- : - x :=
bconditions
homogenity by
  simp
additivity by
  simp; ring
optimality by
  intros x' hx
  simp [hx]

declare_atom Vec.neg [affine] (n : ℕ)& (x : Fin n → ℝ)- : -x :=
bconditions
homogenity by
  ext i; simp
additivity by
  ext i; simp; ring
optimality by
  intros x' hx
  simp [hx]

declare_atom Matrix.neg [affine] (m : ℕ)& (n : ℕ)& (A : Matrix.{0, 0, 0} (Fin m) (Fin n) ℝ)- : -A :=
bconditions
homogenity by
  ext i j; simp
additivity by
  ext i j; simp; ring
optimality by
  intros A' hA i j
  simp [hA i j]

end CvxLean
