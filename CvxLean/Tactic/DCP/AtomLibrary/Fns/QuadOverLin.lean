import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

#check sqrt_le_iff

-- TODO: generalize to x : Fin n → ℝ
-- TODO: distinguish between nonincreasing and nondecreasing.
declare_atom quadOverLin [convex] (x : ℝ)? (y : ℝ)- : x ^ 2 / y :=
vconditions
  (hy : 0 < y)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : soCone (y + t) ![y - t, 2 * x])
solution (t := x ^ 2 / y)
solutionEqualsAtom by rfl
feasibility
  (c : by
    have hynn := le_of_lt hy
    have hx2ynn : 0 ≤ x ^ 2 / y := by
      rw [rpow_two]
      exact div_nonneg (pow_two_nonneg x) hynn
    rw [soCone_add_sub_two_mul_of_nonneg _ hynn hx2ynn]
    unfold soCone
    simp [sqrt_le_iff]
    split_ands
    { apply add_nonneg (le_of_lt hy)
      exact div_nonneg (pow_two_nonneg x) (le_of_lt hy) }
    { have hlhs : (y - x ^ 2 / y) ^ 2 + (2 * x) ^ 2
                = (y ^ 2 + (x ^ 2 / y) ^ 2) + (-(2 * x ^ 2 * (y / y)) + 4 * x ^ 2) := by
        norm_cast; ring
      have hrhs : (y + x ^ 2 / y) ^ 2
                = (y ^ 2 +  (x ^ 2 / y) ^ 2) + (2 * x ^ 2 * (y / y)) := by
        norm_cast; ring
      simp only [←rpow_two]
      rw [hlhs, hrhs, div_self (ne_of_gt hy)]
      apply add_le_add (le_refl _)
      ring_nf!
      exact le_refl _ })
optimality by
  intros y' hyy'
  sorry
vconditionElimination
  (hy : sorry)

end CvxLean
