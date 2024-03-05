import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Matrix

/-!
Trace atom (affine).
-/

namespace CvxLean

declare_atom Matrix.trace [affine] (m : Type)& (hm : Fintype.{0} m)&
(A : Matrix.{0,0,0} m m ℝ)+ : Matrix.trace A:=
bconditions
homogenity by
  rw [Matrix.trace_zero, add_zero, smul_zero, add_zero, Matrix.trace_smul]
additivity by
  rw [Matrix.trace_add, Matrix.trace_zero, add_zero]
optimality by
  intros A' hA
  apply Finset.sum_le_sum
  intros i _
  exact hA i i

end CvxLean
