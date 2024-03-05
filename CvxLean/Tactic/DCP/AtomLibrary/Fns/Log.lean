import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Lib.Math.Data.Vec

/-!
Logarithm atom (concave).
-/

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
  unfold expCone
  simp
  rw [Real.exp_log cond])
optimality by
  intros y hy
  unfold expCone at c_exp
  simp at c_exp
  have hxpos := lt_of_lt_of_le (exp_pos t) c_exp
  have hypos := lt_of_lt_of_le hxpos hy
  have hexptley := le_trans c_exp hy
  exact (le_log_iff_exp_le hypos).2 hexptley
vconditionElimination
  (cond : by
    intros y hy
    unfold expCone at c_exp
    simp at c_exp
    have hexppos := exp_pos t
    have hxpos := lt_of_lt_of_le hexppos c_exp
    exact lt_of_lt_of_le hxpos hy)

open Vec

declare_atom Vec.log [concave] (n : Nat)& (x : (Fin n) → ℝ)+ : log x :=
vconditions (cond : ∀ i, 0 < x i)
implementationVars (t : (Fin n) → ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone t 1 x)
solution (t := log x)
solutionEqualsAtom rfl
feasibility
  (c_exp: by
    dsimp
    unfold Vec.expCone
    intros i
    apply log.feasibility0
    apply cond)
optimality by
  intros x' hx i
  unfold Vec.expCone at c_exp
  apply log.optimality _ _ (c_exp i) _ (hx i)
vconditionElimination (cond : by
  intros x' hx i
  unfold Vec.expCone at c_exp
  apply log.vcondElim0 _ _ (c_exp i) _ (hx i))

end CvxLean
