import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub

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

end CvxLean
