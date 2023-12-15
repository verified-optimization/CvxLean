import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Log
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sum
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecConst
import CvxLean.Lib.Math.LogSumExp

namespace CvxLean

open Real

declare_atom logSumExp [convex] (n : ℕ)& (x : Fin n → ℝ)+ : log (Vec.sum (Vec.exp x)) :=
bconditions
  (hn : 0 < n)
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints
  (c : Vec.sum (Vec.exp (x - Vec.const n t)) ≤ 1)
solution (t := log (Vec.sum (Vec.exp x)))
solutionEqualsAtom by
  rfl;
feasibility
  (c : by
    dsimp
    simp [Vec.sum_exp_eq_sum_div, div_le_iff (Real.exp_pos _)]
    simp [Real.exp_log (Vec.sum_exp_pos hn x)])
optimality by
  intros y hy
  simp [Vec.sum_exp_eq_sum_div, div_le_iff (exp_pos _)] at c
  rw [←log_exp t, log_le_log (Vec.sum_exp_pos hn y) (exp_pos _)]
  refine le_trans ?_ c
  apply Finset.sum_le_sum
  intros i _
  simp [Vec.exp, hy i]
vconditionElimination

declare_atom logSumExp₂ [convex] (x : ℝ)+ (y : ℝ)+ : log ((exp x) + (exp y)) :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints
  (c : log (Vec.sum (Vec.exp ![x, y])) ≤ t)
solution (t := log ((exp x) + (exp y)))
solutionEqualsAtom by
  rfl;
feasibility
  (c : by
    simp [Vec.sum, Vec.exp])
optimality by
  intros x' y' hx' hy'
  simp [Vec.sum, Vec.exp] at c
  refine le_trans ?_ c
  rw [log_le_log (by positivity) (by positivity)]
  apply add_le_add
  { rw [exp_le_exp]; exact hx' }
  { rw [exp_le_exp]; exact hy' }
vconditionElimination
