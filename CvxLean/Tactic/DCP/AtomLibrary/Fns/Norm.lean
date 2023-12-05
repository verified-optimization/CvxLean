import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
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

declare_atom norm2₂ [convex] (x : ℝ)? (y : ℝ)? : sqrt (x ^ 2 + y ^ 2) :=
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : soCone t ![x, y])
solution (t := sqrt (x ^ 2 + y ^ 2))
solutionEqualsAtom by rfl
feasibility
  (c : by simp [soCone])
optimality by
  simp [soCone] at c
  simp [c]
vconditionElimination

lemma norm2₂_eq_norm2 {x y : ℝ} : ‖![x, y]‖ = sqrt (x ^ 2 + y ^ 2) :=
  by simp [Norm.norm]

end CvxLean
