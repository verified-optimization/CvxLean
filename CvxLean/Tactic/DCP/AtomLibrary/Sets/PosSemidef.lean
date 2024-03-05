import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones

/-!
Atom for positive semidefinite constraints (convex set).

This can be seen as an alias for `Matrix.PSDCone`, really.
-/

namespace CvxLean

declare_atom Matrix.PosSemidef [convex_set] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)? : Matrix.PosSemidef A :=
vconditions
implementationVars
implementationObjective Real.Matrix.PSDCone A
implementationConstraints
solution
solutionEqualsAtom by rw [Real.Matrix.PSDCone]
feasibility
optimality by rw [Real.Matrix.PSDCone]
vconditionElimination

end CvxLean
