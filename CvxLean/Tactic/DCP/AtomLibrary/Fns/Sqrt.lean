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
    simp [rotatedSoCone]
    refine ⟨?_, cond, zero_le_two⟩
    rw [sq_sqrt cond])
optimality by
  intros y hy
  simp [rotatedSoCone] at c1
  have h := c1.1
  exact Real.le_sqrt_of_sq_le (le_trans h hy)
vconditionElimination (cond : fun _ hx => c1.2.1.trans hx)

end CvxLean
