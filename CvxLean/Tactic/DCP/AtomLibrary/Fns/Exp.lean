import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

set_option trace.Meta.debug true
declare_atom exp [convex] (x : ℝ)+ : Real.exp x :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone x 1 t)
solution (t := exp x)
solutionEqualsAtom by
  rfl;
feasibility
  (c_exp : by simp [expCone])
optimality by
  intros x' hx
  rw [←exp_iff_expCone] at c_exp
  have hexpleexp := exp_le_exp.2 hx
  exact hexpleexp.trans c_exp
vconditionElimination

open Vec

declare_atom Vec.exp [convex] (n : Nat)& (x : (Fin n) → ℝ)+ : exp x :=
vconditions
implementationVars (t : Fin n → ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone x 1 t)
solution (t := exp x)
solutionEqualsAtom
  rfl
feasibility
  (c_exp: by
    intros _ i
    apply exp.feasibility0)
optimality by
  intros x' hx i
  apply exp.optimality _ _ (c_exp i) _ (hx i)
vconditionElimination

end CvxLean
