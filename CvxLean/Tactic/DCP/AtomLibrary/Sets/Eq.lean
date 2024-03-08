import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub

/-!
Equality atom (convex set).

Note that we do not distinguish between affine and convex sets.
-/

namespace CvxLean

declare_atom eq [convex_set] (x : ℝ)? (y : ℝ)? : x = y :=
vconditions
implementationVars
implementationObjective Real.zeroCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  exact Iff.intro Eq.symm Eq.symm
feasibility
optimality by
  unfold Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  exact Eq.symm
vconditionElimination

declare_atom Vec.eq [convex_set] (n : ℕ)& (x : Fin n → ℝ)? (y : Fin n → ℝ)? : x = y :=
vconditions
implementationVars
implementationObjective Real.Vec.zeroCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Vec.zeroCone Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  aesop
feasibility
optimality by
  unfold Real.Vec.zeroCone Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  aesop
vconditionElimination

declare_atom Matrix.eq [convex_set] (m : ℕ)& (n : ℕ)& (X : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)?
  (Y : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)? : X = Y :=
vconditions
implementationVars
implementationObjective Real.Matrix.zeroCone (Y - X)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Matrix.zeroCone Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  aesop
feasibility
optimality by
  unfold Real.Matrix.zeroCone Real.zeroCone
  simp [sub_eq_iff_eq_add, zero_add]
  aesop
vconditionElimination

end CvxLean
