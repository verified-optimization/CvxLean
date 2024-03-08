import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp
import CvxLean.Lib.Math.Data.Vec

/-!
Geometric mean atom (concave).
-/

namespace CvxLean

open Real

-- TODO: generalize to x : Fin n → ℝ
declare_atom geoMean [concave] (x : ℝ)+ (y : ℝ)+ : sqrt (x * y) :=
vconditions
  (hx : 0 ≤ x)
  (hy : 0 ≤ y)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : soCone (x + y) ![x - y, 2 * t])
  (c2 : 0 ≤ t)
  (c3 : 0 ≤ x)
  (c4 : 0 ≤ y)
solution (t := sqrt (x * y))
solutionEqualsAtom by rfl
feasibility
  (c1 : by
    rw [soCone_add_sub_two_mul_of_nonneg _ hx hy, rpow_two, sq_sqrt]
    exact mul_nonneg hx hy)
  (c2 : by
    exact sqrt_nonneg _)
  (c3 : hx)
  (c4 : hy)
optimality by
  intros v w hxv hyw
  have hv := le_trans c3 hxv
  have hw := le_trans c4 hyw
  rw [soCone_add_sub_two_mul_of_nonneg _ c3 c4, rpow_two] at c1
  rw [le_sqrt c2 (mul_nonneg hv hw)]
  exact le_trans c1 (mul_le_mul hxv hyw c4 hv)
vconditionElimination
  (hx : by
    intros v _ hxv _
    exact le_trans c3 hxv)
  (hy : by
    intros _ w _ hyw
    exact le_trans c4 hyw)

end CvxLean
