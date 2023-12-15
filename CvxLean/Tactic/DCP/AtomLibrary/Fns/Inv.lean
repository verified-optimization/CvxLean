import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Power

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

end CvxLean
