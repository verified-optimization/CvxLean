import CvxLean.Tactic.DCP.AtomCmdimport CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

declare_atom max [convex] (x : ℝ)+ (y : ℝ)+ : max x y :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints
  (c1 : x ≤ t)
  (c2 : y ≤ t)
solution (t := max x y)
solutionEqualsAtom by
  rfl;
feasibility
  (c1 : by simp)
  (c2 : by simp)
optimality by
  intros x' y' hx' hy'
  rw [max_le_iff]
  split_ands <;> linarith
vconditionElimination

end CvxLean
