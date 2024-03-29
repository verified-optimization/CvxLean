import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Lib.Math.Data.Matrix

/-!
Absolute value atom (convex).
-/

namespace CvxLean

open Real

declare_atom abs [convex] (x : ℝ)? : abs x :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints
  (c_pos : nonnegOrthCone (t - x))
  (c_neg : nonnegOrthCone (t + x))
solution (t := abs x)
solutionEqualsAtom rfl
feasibility
  (c_pos : by
    unfold nonnegOrthCone
    rw [sub_nonneg]
    exact le_abs_self x)
  (c_neg : by
    unfold nonnegOrthCone
    rw [← neg_le_iff_add_nonneg']
    exact neg_abs_le x)
optimality by
  apply abs_le.2
  rw [← sub_nonneg, sub_neg_eq_add, add_comm, ← sub_nonneg (b := x)]
  unfold nonnegOrthCone at c_pos c_neg
  exact ⟨c_neg, c_pos⟩
vconditionElimination

declare_atom Vec.abs [convex] (n : Nat)& (x : (Fin n) → ℝ)? : abs x :=
vconditions
implementationVars (t : (Fin n) → ℝ)
implementationObjective t
implementationConstraints
  (c_pos : Real.Vec.nonnegOrthCone (t - x : (Fin n) → ℝ))
  (c_neg : Real.Vec.nonnegOrthCone (t + x : (Fin n) → ℝ))
solution (t := abs x)
solutionEqualsAtom rfl
feasibility
  (c_pos : by
    unfold Real.Vec.nonnegOrthCone
    intros
    apply abs.feasibility0)
  (c_neg : by
    unfold Real.Vec.nonnegOrthCone
    intros
    apply abs.feasibility1)
optimality by
  intros i
  unfold Real.Vec.nonnegOrthCone at c_pos c_neg
  apply abs.optimality _ _ (c_pos i) (c_neg i)
vconditionElimination

declare_atom Matrix.abs [convex] (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)? :
  M.abs :=
vconditions
implementationVars (T : Matrix (Fin m) (Fin n) ℝ)
implementationObjective T
implementationConstraints
  (c_pos : Real.Matrix.nonnegOrthCone (T - M : Matrix (Fin m) (Fin n) ℝ))
  (c_neg : Real.Matrix.nonnegOrthCone (T + M : Matrix (Fin m) (Fin n) ℝ))
solution (T := M.abs)
solutionEqualsAtom rfl
feasibility
  (c_pos : by
    unfold Real.Matrix.nonnegOrthCone
    intros _ _ _
    apply abs.feasibility0)
  (c_neg :  by
    unfold Real.Matrix.nonnegOrthCone
    intros _ _ _
    apply abs.feasibility1)
optimality by
  intros i j
  unfold Real.Matrix.nonnegOrthCone at c_pos c_neg
  apply abs.optimality _ _ (c_pos i j) (c_neg i j)
vconditionElimination

end CvxLean
