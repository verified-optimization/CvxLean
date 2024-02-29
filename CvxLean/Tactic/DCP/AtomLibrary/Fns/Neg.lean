import CvxLean.Tactic.DCP.AtomCmd
namespace CvxLean

declare_atom neg [affine] (x : ℝ)- : - x :=
bconditions
homogenity by
  simp [neg_zero, add_zero]
additivity by
  rw [neg_add]
  simp
optimality by
  intros x' hx
  apply neg_le_neg hx

end CvxLean
