import CvxLean.Tactic.DCP.AtomCmdimport CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub

namespace CvxLean

declare_atom eq [convex_set] (x : ℝ)? (y : ℝ)? : x = y :=
vconditions
implementationVars
implementationObjective Real.zeroCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  exact Iff.intro Eq.symm Eq.symm
feasibility
optimality by
  unfold Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  exact Eq.symm
vconditionElimination

end CvxLean
