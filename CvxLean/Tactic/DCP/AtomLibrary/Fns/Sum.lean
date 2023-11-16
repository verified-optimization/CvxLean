import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Vec
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

open Vec in

declare_atom Vec.sum [affine] (m : Nat)& (x : Fin m → ℝ)+ : sum x :=
bconditions
homogenity by
  unfold Vec.sum
  simp only [Pi.zero_apply]
  rw [Finset.smul_sum, Finset.sum_const_zero, add_zero, smul_zero, add_zero]
  rfl
additivity by
  unfold Vec.sum
  simp only [Pi.zero_apply, Pi.add_apply]
  rw [Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
optimality by
  intro x' hx
  apply Finset.sum_le_sum
  intros _ _
  apply hx

open Matrix in

declare_atom Matrix.sum [affine] (m : Nat)&
  (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)+ : sum X :=
bconditions
homogenity by
  unfold Matrix.sum
  simp only [zero_apply, Finset.sum_const_zero, Finset.smul_sum]
  simp [smul_zero, add_zero]
additivity by
  unfold Matrix.sum
  simp only [zero_apply, Finset.sum_const_zero, Finset.smul_sum]
  simp [add_zero, Finset.sum_add_distrib]
optimality by
  intros X' hX
  apply Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  apply hX

end CvxLean
