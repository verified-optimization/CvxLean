import CvxLean.Tactic.DCP.AtomCmdimport CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Power
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Transpose

namespace CvxLean

open Real

-- TODO: These are just the same as `powNegOne`. We need them for pattern
-- mathcing. The issue is that implementationConstraints does not know about
-- vconditions. If we fix that, then we can just say (c : x ^ (-1) ≤ t).

declare_atom inv [convex] (x : ℝ)- : x⁻¹ :=
vconditions
  (hx : 0 < x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : soCone (t + x) ![t - x, 2])
  (c2 : 0 ≤ t)
  (c3 : 0 ≤ x)
solution
  (t := x⁻¹)
solutionEqualsAtom rfl
feasibility
  (c1 : by
    rw [Real.inv_eq_pow_neg_one hx]
    exact powNegOne.feasibility0 x hx)
  (c2 : by
    rw [Real.inv_eq_pow_neg_one hx]
    have hinv : 0 < x ^ (-1 : ℝ) := by rwa [rpow_neg_one, inv_pos]
    exact le_of_lt hinv)
  (c3 : le_of_lt hx)
optimality by
  intros y hy
  rw [soCone_add_sub_two_of_nonneg c2 c3] at c1
  have hxpos : 0 < x := by
    cases (lt_or_eq_of_le c3) with
    | inl h => exact h
    | inr h => rw [←h] at c1; linarith
  have hypos := lt_of_lt_of_le hxpos hy
  rw [inv_eq_pow_neg_one hypos]
  rw [rpow_neg_one, inv_eq_one_div, div_le_iff hypos]
  apply le_trans c1
  apply mul_le_mul_of_nonneg_left hy c2
vconditionElimination
  (hx : by
    intros y hy
    rw [soCone_add_sub_two_of_nonneg c2 c3] at c1
    cases (lt_or_eq_of_le c3) with
      | inl h => linarith
      | inr h => rw [←h] at c1; linarith)

declare_atom oneDiv [convex] (x : ℝ)- : 1 / x :=
vconditions
  (hx : 0 < x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : soCone (t + x) ![t - x, 2])
  (c2 : 0 ≤ t)
  (c3 : 0 ≤ x)
solution
  (t := 1 / x)
solutionEqualsAtom rfl
feasibility
  (c1 : by
    rw [Real.one_div_eq_pow_neg_one hx]
    exact powNegOne.feasibility0 x hx)
  (c2 : by
    rw [Real.one_div_eq_pow_neg_one hx]
    have hinv : 0 < x ^ (-1 : ℝ) := by rwa [rpow_neg_one, inv_pos]
    exact le_of_lt hinv)
  (c3 : le_of_lt hx)
optimality by
  intros y hy
  rw [soCone_add_sub_two_of_nonneg c2 c3] at c1
  have hxpos : 0 < x := by
    cases (lt_or_eq_of_le c3) with
    | inl h => exact h
    | inr h => rw [←h] at c1; linarith
  have hypos := lt_of_lt_of_le hxpos hy
  rw [one_div_eq_pow_neg_one hypos]
  rw [rpow_neg_one, inv_eq_one_div, div_le_iff hypos]
  apply le_trans c1
  apply mul_le_mul_of_nonneg_left hy c2
vconditionElimination
  (hx : by
    intros y hy
    rw [soCone_add_sub_two_of_nonneg c2 c3] at c1
    cases (lt_or_eq_of_le c3) with
      | inl h => linarith
      | inr h => rw [←h] at c1; linarith)

open Matrix

-- TODO: Repetition with `powNegOne`.
declare_atom Vec.oneDiv [convex] (n : ℕ)& (x : Fin n → ℝ)- : 1 / x :=
vconditions
  (hx : StrongLT 0 x)
implementationVars (t : Fin n → ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : Vec.soCone (t + x) (![t - x, 2]ᵀ))
  (c2 : 0 ≤ t)
  (c3 : 0 ≤ x)
solution
  (t := 1 / x)
solutionEqualsAtom rfl
feasibility
  (c1 : by
    intros t i
    rw [vec_soCone_apply_to_soCone_add_sub_two]
    dsimp
    rw [Real.one_div_eq_pow_neg_one (hx i)]
    exact powNegOne.feasibility0 (x i) (hx i))
  (c2 : by
    intros t i
    dsimp
    rw [Real.one_div_eq_pow_neg_one (hx i)]
    have hinv : 0 < (x i) ^ (-1 : ℝ) := by rw [rpow_neg_one, inv_pos]; exact hx i
    exact le_of_lt hinv)
  (c3 : le_of_strongLT hx)
optimality by
  intros y hy i; dsimp
  have c1i := c1 i
  rw [vec_soCone_apply_to_soCone_add_sub_two] at c1i
  rw [soCone_add_sub_two_of_nonneg (c2 i) (c3 i)] at c1i
  have hxipos : 0 < x i := by
    cases (lt_or_eq_of_le (c3 i)) with
    | inl h => exact h
    | inr h => simp [←h] at c1i; linarith
  have hyipos := lt_of_lt_of_le hxipos (hy i)
  rw [one_div_eq_pow_neg_one hyipos]
  rw [rpow_neg_one, inv_eq_one_div, div_le_iff hyipos]
  apply le_trans c1i
  apply mul_le_mul_of_nonneg_left hy c2
vconditionElimination
  (hx : by
    intros y hy i
    have c1i := c1 i
    rw [vec_soCone_apply_to_soCone_add_sub_two] at c1i
    rw [soCone_add_sub_two_of_nonneg (c2 i) (c3 i)] at c1i
    cases (lt_or_eq_of_le (c3 i)) with
      | inl h =>
          have hyi := hy i
          simp at h hyi ⊢; linarith
      | inr h => simp [←h] at c1i; linarith)

end CvxLean
