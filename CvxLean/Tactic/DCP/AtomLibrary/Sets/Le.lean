import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub

namespace CvxLean

declare_atom le [convex_set] (x : ℝ)- (y : ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.posOrthCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.posOrthCone
  simp
feasibility
optimality by
  intros x' y' hx hy h
  unfold Real.posOrthCone at h
  simp at h
  exact (hx.trans h).trans hy
vconditionElimination

declare_atom Vec.le [convex_set] (n : Nat)& (x : (Fin n) → ℝ)- (y : (Fin n) → ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.Vec.posOrthCone (y - x : (Fin n) → ℝ)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Vec.posOrthCone
  unfold Real.posOrthCone
  rw [← iff_iff_eq]
  constructor
  · intros h i
    rw [← le.solEqAtom]
    unfold Real.posOrthCone
    apply h
  · intros hy i
    simp [hy i]
feasibility
optimality by
  intros x' y' hx hy h i
  unfold Real.Vec.posOrthCone at h
  exact le.optimality _ _ _ _ (hx i) (hy i) (h i)
vconditionElimination

end CvxLean
