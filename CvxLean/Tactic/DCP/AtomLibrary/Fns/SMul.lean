import CvxLean.Tactic.DCP.Atoms

namespace CvxLean

declare_atom Nat.smul [affine] (n : ℕ)& (x : ℝ)+ :
  n • x :=
bconditions
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality by
  intros y' hy
  apply smul_le_smul_of_nonneg hy (Nat.zero_le _)

declare_atom Nat.Vec.smul [affine] (n : ℕ)& (k : ℕ)& (x : Fin n → ℝ)+ :
  k • x :=
bconditions
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality by
  intros y' hy i
  exact smul_le_smul_of_nonneg (hy i) (Nat.zero_le _)

declare_atom Real.Vec.smul1 [affine] (n : ℕ)& (k : ℝ)& (x : Fin n → ℝ)+ :
  k • x :=
bconditions
  (hk : 0 ≤ k)
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality by
  intros y' hy
  apply smul_le_smul_of_nonneg hy hk

declare_atom Real.Vec.smul2 [affine] (n : ℕ)& (k : ℝ)& (x : Fin n → ℝ)- :
  k • x :=
bconditions
  (hk : k ≤ 0)
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality by
  intros y' hy
  apply smul_le_smul_of_nonpos hy hk

declare_atom Real.Vec.smul3 [affine] (n : ℕ)& (k : ℝ)& (x : Fin n → ℝ)? :
  k • x :=
bconditions
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality le_refl _

end CvxLean
