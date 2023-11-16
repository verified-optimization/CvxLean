import CvxLean.Tactic.DCP.Atoms

namespace CvxLean

open Real

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

end CvxLean
