import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones

namespace CvxLean

open Real

declare_atom log [concave] (x : ℝ)+ : log x :=
vconditions (cond : 0 < x)
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone t 1 x)
solution (t := log x)
solutionEqualsAtom by
  rfl;
feasibility (c_exp : by
  simp [expCone]
  rw [Real.exp_log cond])
optimality by
  intros y hy
  simp [expCone] at c_exp
  have hxpos := lt_of_lt_of_le (exp_pos t) c_exp
  have hypos := lt_of_lt_of_le hxpos hy
  have hexptley := le_trans c_exp hy
  exact (le_log_iff_exp_le hypos).2 hexptley
vconditionElimination
  (cond : by
    intros y hy
    simp [expCone] at c_exp
    have hexppos := exp_pos t
    have hxpos := lt_of_lt_of_le hexppos c_exp
    exact lt_of_lt_of_le hxpos hy)

declare_atom Vec.log [concave] (n : Nat)& (x : (Fin n) → ℝ)+ : log x :=
vconditions (cond : ∀ i, 0 < x i)
implementationVars (t : (Fin n) → ℝ)
implementationObjective t
implementationConstraints (c_exp : Real.Vec.expCone t 1 x)
solution (t := log x)
solutionEqualsAtom rfl
feasibility
  (c_exp: by
    intros _ i
    apply log.feasibility0
    apply cond)
optimality by
  intros x' hx i
  apply log.optimality _ _ (c_exp i) _ (hx i)
vconditionElimination (cond : by
  intros x' hx i
  apply log.vcondElim0 _ _ (c_exp i) _ (hx i))

end CvxLean
