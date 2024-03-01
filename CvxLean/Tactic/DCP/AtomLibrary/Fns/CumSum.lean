import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Vec

declare_atom Vec.cumsum [affine] (n : Nat)& (x : Fin n → ℝ)+ : cumsum x :=
bconditions
homogenity by
  unfold Vec.cumsum; split_ifs
  . funext i; simp [Finset.mul_sum]
  . ring
additivity by
  unfold Vec.cumsum; split_ifs
  . funext i; simp [Finset.sum_add_distrib]
  . ring
optimality by
  intro x' hxx'
  unfold Vec.cumsum; split_ifs
  . intros i; apply Finset.sum_le_sum; intros j _; exact hxx' j
  . simp

end CvxLean
