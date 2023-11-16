import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones

namespace CvxLean

declare_atom Matrix.PosSemidef [convex_set]
  (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)?
  : Matrix.PosSemidef A :=
vconditions
implementationVars
implementationObjective Real.Matrix.PSDCone A
implementationConstraints
solution
solutionEqualsAtom by simp [Real.Matrix.PSDCone]
feasibility
optimality by simp [Real.Matrix.PSDCone]
vconditionElimination

end CvxLean
