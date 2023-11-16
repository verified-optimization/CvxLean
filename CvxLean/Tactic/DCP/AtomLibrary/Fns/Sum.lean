import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

open BigOperators

-- TODO: Do I need Vec.sum from missing?
declare_atom Vec.sum [affine] (m : Nat)& (x : Fin m → ℝ)+ : ∑ i, x i :=
bconditions
homogenity by
  simp only [Pi.zero_apply]
  rw [Finset.smul_sum, Finset.sum_const_zero, add_zero, smul_zero, add_zero]
  rfl
additivity by
  simp only [Pi.zero_apply, Pi.add_apply]
  rw [Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
optimality by
  intro x' hx
  apply Finset.sum_le_sum
  intros _ _
  apply hx

-- TODO: Do I need Matrix.sum from missing?
declare_atom Matrix.sum [affine] (m : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)+ : ∑ i, (∑ j, X i j) :=
bconditions
homogenity by
  simp only [Matrix.zero_apply, Finset.sum_const_zero, Finset.smul_sum]
  simp [smul_zero, add_zero]
additivity by
  simp only [Matrix.zero_apply, Finset.sum_const_zero, Finset.smul_sum]
  simp [add_zero, Finset.sum_add_distrib]
optimality by
  intros X' hX
  apply Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  apply hX

end CvxLean
