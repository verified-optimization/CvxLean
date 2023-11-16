import CvxLean.Tactic.DCP.Atoms

namespace CvxLean

declare_atom smul [affine] (n : ℕ)& (y : ℝ)+ : n • y :=
bconditions
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality by
  intros y' hy
  apply smul_le_smul_of_nonneg hy (Nat.zero_le _)

end CvxLean
