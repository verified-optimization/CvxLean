import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Eq
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sq
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Abs
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

declare_atom huber1 [convex] (x : ℝ)? : huber x 1 :=
vconditions
implementationVars (v : ℝ) (w : ℝ)
implementationObjective (2 * v + w ^ 2)
implementationConstraints
  (c1 : |x| ≤ v + w)
  (c2 : 0 ≤ w)
  (c3 : w ≤ 1)
  (c4 : 0 ≤ v)
solution
  (v := if |x| ≤ 1 then 0 else |x| - 1)
  (w := if |x| ≤ 1 then |x| else 1)
solutionEqualsAtom by
  simp [huber]
  split_ifs <;> ring
feasibility
  (c1 : by
    split_ifs <;> linarith)
  (c2 : by
    split_ifs <;> norm_num)
  (c3 : by
    split_ifs <;> linarith)
  (c4 : by
    split_ifs <;> linarith)
optimality by
  simp [huber]
  split_ifs with h
  { by_cases hca : w ≤ |x|
    {
      rw [←sub_le_iff_le_add]
      have : |x| ^ 2 - w ^ 2 = (|x| + w) * (|x| - w) := by ring_nf; simp
      rw [←sq_abs]
      rw [←rpow_two, ←rpow_two, this]
      apply mul_le_mul
      { linarith }
      { linarith }
      { linarith }
      { norm_num }
    }
    {
      replace hca := not_le.mp hca
      by_cases hxz : x = 0
      {
        rw [hxz]
        simp
        apply add_nonneg <;> norm_num [c2, c4]
      }
      have hcx : 0 < |x| := abs_pos.mpr hxz
      have hx2 := mul_lt_mul hca (le_of_lt hca) hcx c2
      rw [←pow_two, sq_abs, ←pow_two] at hx2
      have hv : 0 ≤ 2 * v := by linarith
      have := add_le_add (le_of_lt hx2) hv
      linarith
    }
   }
  { replace h := not_le.mp h
    have h1 : 2 * |x| - 1  ≤ 2 * v + (2 * w - 1) := by linarith
    apply le_trans h1
    apply add_le_add (le_refl _)
    rw [←zero_add (_ - _)]
    rw [←le_sub_iff_add_le ]
    have h2 : w * w - (2 * w - 1) = (w - 1) * (w - 1) := by ring_nf
    rw [pow_two]
    rw [h2]
    exact mul_self_nonneg _
  }
vconditionElimination

end CvxLean
