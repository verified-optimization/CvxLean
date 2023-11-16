import CvxLean.Tactic.DCP.Atoms

namespace CvxLean

declare_atom maximizeNeg [affine] (x : ℝ)- : maximizeNeg x :=
bconditions
homogenity by
  simp [maximizeNeg, neg_zero, add_zero]
additivity by
  unfold maximizeNeg
  rw [neg_add]
  simp
optimality by
  intros x' hx
  apply neg_le_neg hx

end CvxLean
