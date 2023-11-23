import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

declare_atom norm2 [convex] (n : Nat)& (x : Fin n → ℝ)? : ‖x‖ :=
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : soCone t x)
solution (t := ‖x‖)
solutionEqualsAtom by rfl
feasibility
  (c : by
    unfold soCone
    simp [Norm.norm])
optimality by
  unfold soCone at c
  simp [Norm.norm] at c ⊢
  exact c
vconditionElimination

end CvxLean
