import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons

namespace CvxLean

open Real

declare_atom sqrt [concave] (x : ℝ)+ : Real.sqrt x :=
vconditions (cond : 0 ≤ x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : rotatedSoCone x (1/2) ![t])
solution (t := Real.sqrt x)
solutionEqualsAtom by
  rfl;
feasibility
  (c1 : by
    dsimp
    unfold rotatedSoCone
    refine ⟨?_, cond, by norm_num⟩
    simp
    rw [sq_sqrt cond])
optimality by
  intros y hy
  unfold rotatedSoCone at c1
  simp at c1
  have h := c1.1
  exact Real.le_sqrt_of_sq_le (le_trans h hy)
vconditionElimination (cond : by
  intros _ hx
  unfold rotatedSoCone at c1
  exact c1.2.1.trans hx)

end CvxLean
