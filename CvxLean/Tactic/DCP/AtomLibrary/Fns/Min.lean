import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

declare_atom min [concave] (x : ℝ)+ (y : ℝ)+ : min x y :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints
  (c1 : t ≤ x)
  (c2 : t ≤ y)
solution (t := min x y)
solutionEqualsAtom by
  rfl;
feasibility
  (c1 : by simp)
  (c2 : by simp)
optimality by
  intros x' y' hx' hy'
  rw [le_min_iff]
  split_ands <;> linarith
vconditionElimination

end CvxLean
