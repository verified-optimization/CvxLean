import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Lib.Math.Data.Matrix

/-!
Inequality atoms (convex set).

Note that we do not distinguish between affine and convex sets.
-/

namespace CvxLean

declare_atom le [convex_set] (x : ℝ)- (y : ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.nonnegOrthCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.nonnegOrthCone
  simp
feasibility
optimality by
  intros x' y' hx hy h
  unfold Real.nonnegOrthCone at h
  simp at h
  exact (hx.trans h).trans hy
vconditionElimination

declare_atom Vec.le [convex_set] (n : Nat)& (x : (Fin n) → ℝ)- (y : (Fin n) → ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.Vec.nonnegOrthCone (y - x : (Fin n) → ℝ)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Vec.nonnegOrthCone
  unfold Real.nonnegOrthCone
  rw [← iff_iff_eq]
  constructor
  · intros h i
    rw [← le.solEqAtom]
    unfold Real.nonnegOrthCone
    apply h
  · intros hy i
    simp [hy i]
feasibility
optimality by
  intros x' y' hx hy h i
  unfold Real.Vec.nonnegOrthCone at h
  exact le.optimality _ _ _ _ (hx i) (hy i) (h i)
vconditionElimination

declare_atom Vec.le' [convex_set] (n : Nat)& (x : (Fin n) → ℝ)- (y : (Fin n) → ℝ)+ :
    ∀ i, x i ≤ y i :=
vconditions
implementationVars
implementationObjective Real.Vec.nonnegOrthCone (y - x : (Fin n) → ℝ)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Vec.nonnegOrthCone
  unfold Real.nonnegOrthCone
  rw [← iff_iff_eq]
  constructor
  · intros h i
    rw [← le.solEqAtom]
    unfold Real.nonnegOrthCone
    apply h
  · intros hy i
    simp [hy i]
feasibility
optimality by
  intros x' y' hx hy h i
  unfold Real.Vec.nonnegOrthCone at h
  exact le.optimality _ _ _ _ (hx i) (hy i) (h i)
vconditionElimination

declare_atom Matrix.le [convex_set] (m : Nat)& (n : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)-
    (Y : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)+ : X ≤ Y :=
vconditions
implementationVars
implementationObjective Real.Matrix.nonnegOrthCone (Y - X)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Matrix.nonnegOrthCone Real.nonnegOrthCone
  aesop
feasibility
optimality by
  intros X' Y' hX hY h i j
  unfold Real.Matrix.nonnegOrthCone Real.nonnegOrthCone at h
  have hij := h i j
  have hXij := hX i j
  have hYij := hY i j
  simp at hij hXij hYij
  linarith
vconditionElimination

end CvxLean
