import CvxLean.Tactic.DCP.Atoms

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

end CvxLean
