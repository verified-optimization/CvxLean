import CvxLean.Tactic.DCP.Atoms

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

-- TODO: Is this somewhere in mathlib?
instance [Preorder α] : Preorder (Matrix m n α) :=
{ le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_refl _
  le_trans := fun _ _ _ hAB hBC i j => le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _ }

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
