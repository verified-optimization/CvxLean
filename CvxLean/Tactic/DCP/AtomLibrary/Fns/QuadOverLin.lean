import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

-- TODO(RFM): generalize to x : Fin n → ℝ
-- TODO(RFM): distinguish between nonincreasing and nondecreasing.
declare_atom quadOverLin [convex] (x : ℝ)? (y : ℝ)- : x ^ 2 / y :=
vconditions
  (hy : 0 < y)
implementationVars (t : ℝ) (y' : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : soCone (y + t) ![y - t, 2 * x])
  (c2 : 0 ≤ t)
  -- NOTE(RFM): This is a trick to make y strictly positive.
  -- TODO(RFM): This makes the solver stall (error 166).
  -- (c3 : exp y' ≤ y)
solution (t := x ^ 2 / y) (y' := log y)
solutionEqualsAtom by rfl
feasibility
  (c1 : by
    have hynn := le_of_lt hy
    have hx2ynn : 0 ≤ x ^ 2 / y := by
      rw [rpow_two]; exact div_nonneg (pow_two_nonneg x) hynn
    rw [soCone_add_sub_two_mul_of_nonneg _ hynn hx2ynn]
    rw [mul_div, mul_comm, ←mul_div, div_self (ne_of_gt hy), mul_one])
  (c2 : by
    have hynn := le_of_lt hy
    rw [rpow_two]
    exact div_nonneg (pow_two_nonneg x) hynn)
  -- (c3 : by
  --   simp [exp_log hy])
optimality by
  intros z hyz
  have hy : 0 < y := sorry --lt_of_lt_of_le (exp_pos _) c3
  have hynn := le_of_lt hy
  rw [soCone_add_sub_two_mul_of_nonneg x hynn c2] at c1
  have hz := lt_of_lt_of_le hy hyz
  rw [div_le_iff' hz]
  apply le_trans c1
  apply mul_le_mul hyz (le_refl _) c2 (le_of_lt hz)
vconditionElimination
  (hy : by
    -- intros z hz
    -- have hy := lt_of_lt_of_le (exp_pos _) c3
    -- exact lt_of_lt_of_le hy hz
    sorry)

end CvxLean
