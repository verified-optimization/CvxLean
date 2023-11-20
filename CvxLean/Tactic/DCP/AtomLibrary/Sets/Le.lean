import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub

namespace CvxLean

declare_atom le [convex_set] (x : ℝ)+ (y : ℝ)- : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.posOrthCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by
  simp [Real.posOrthCone]
feasibility
optimality by
  intros x' y' hx hy h
  simp [Real.posOrthCone] at h
  exact (hx.trans h).trans hy
vconditionElimination

declare_atom Vec.le [convex_set] (n : Nat)& (x : (Fin n) → ℝ)+ (y : (Fin n) → ℝ)- : x ≤ y :=
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
    apply h
  · intros h i
    erw [le.solEqAtom]
    apply h
feasibility
optimality by
  intros x' y' hx hy h i
  apply le.optimality _ _ _ _ (hx i) (hy i) (h i)
vconditionElimination

end CvxLean
