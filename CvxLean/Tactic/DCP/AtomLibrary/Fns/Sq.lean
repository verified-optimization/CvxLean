import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons

namespace CvxLean

open Real

declare_atom sq [convex] (x : ℝ)? : x ^ 2 :=
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : rotatedSoCone t (1/2) ![x])
solution
  (t := x ^ 2)
solutionEqualsAtom rfl
feasibility
  (c1 : by
    simp [rotatedSoCone]
    exact ⟨sq_nonneg x, zero_le_two⟩)
optimality by
  have h := c1.1
  simp at h ⊢
  exact h
vconditionElimination

end CvxLean
