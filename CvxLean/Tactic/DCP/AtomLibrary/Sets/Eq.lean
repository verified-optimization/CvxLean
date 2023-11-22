import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub

namespace CvxLean

declare_atom eq [convex_set] (x : ℝ)? (y : ℝ)? : x = y :=
vconditions
implementationVars
implementationObjective Real.zeroCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  simp [Real.zeroCone, sub_eq_iff_eq_add, zero_add]
  exact Iff.intro Eq.symm Eq.symm;
feasibility
optimality by
  simp [Real.zeroCone, sub_eq_iff_eq_add, zero_add]
  exact Eq.symm
vconditionElimination

end CvxLean
