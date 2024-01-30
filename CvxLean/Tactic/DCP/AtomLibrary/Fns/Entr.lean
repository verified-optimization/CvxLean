import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

declare_atom entr [concave] (x : ℝ)? : -(x * log x) :=
vconditions (cond : 0 ≤ x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : expCone t x 1)
solution (t := -(x * log x))
solutionEqualsAtom by rfl
feasibility
  (c : by
    unfold expCone
    cases (lt_or_eq_of_le cond) with
    | inl h =>
        left
        refine ⟨h, ?_⟩
        rw [neg_div, mul_comm _ (log x), ←mul_div]
        rw [div_self (ne_of_lt h).symm, mul_one, exp_neg, exp_log h]
        rw [inv_eq_one_div, mul_div, mul_one, div_self (ne_of_lt h).symm]
    | inr h =>
        replace h := h.symm
        right
        refine ⟨h, ?_⟩
        simp [h])
optimality by
  unfold expCone at c
  cases c with
  | inl c =>
      rw [mul_comm, ←neg_mul, ←div_le_iff c.1]
      rw [←exp_le_exp, exp_neg, exp_log c.1, inv_eq_one_div]
      rw [le_div_iff c.1, mul_comm]
      exact c.2
  | inr c =>
      simp [entr, c.1, c.2]
vconditionElimination
  (cond : by
    unfold expCone at c
    cases c with
    | inl c => exact le_of_lt c.1
    | inr c => exact le_of_eq c.1.symm)

declare_atom entr2 [concave] (x : ℝ)? : entr x :=
vconditions (cond : 0 ≤ x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c : expCone t x 1)
solution (t := Real.entr x)
solutionEqualsAtom by rfl
feasibility
  (c : entr.feasibility0 x cond)
optimality entr.optimality x t c
vconditionElimination
  (cond : entr.vcondElim0 x t c)

declare_atom Vec.entr [concave] (m : Nat)& (x : Fin m → ℝ)? : Vec.entr x :=
vconditions (cond : 0 ≤ x)
implementationVars (t : Fin m → ℝ)
implementationObjective (t)
implementationConstraints
  (c : Vec.expCone t x 1)
solution (t := Vec.entr x)
solutionEqualsAtom by rfl
feasibility
  (c : by
    unfold Vec.expCone Vec.entr
    intros _ i
    exact entr.feasibility0 (x i) (cond i))
optimality by
  unfold Vec.expCone at c
  unfold Vec.entr
  intros i
  exact entr.optimality (x i) (t i) (c i)
vconditionElimination
  (cond : by
    unfold Vec.expCone at c
    intros i
    exact entr.vcondElim0 (x i) (t i) (c i))

end CvxLean
