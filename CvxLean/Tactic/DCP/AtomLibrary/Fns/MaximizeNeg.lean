import CvxLean.Tactic.DCP.AtomCmd

/-!
`maximizeNeg` is just negation, really, but needs its own atom as it has its own identifier
(affine).
-/

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
