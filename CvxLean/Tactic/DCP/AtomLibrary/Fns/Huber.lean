import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Eq
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sq
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Abs
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.SMul
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

declare_atom huber [convex] (x : ℝ)? : huber x :=
vconditions
implementationVars (v : ℝ) (w : ℝ)
implementationObjective (2 * v + w ^ 2)
implementationConstraints
  (c1 : |x| ≤ v + w)
  (c2 : 0 ≤ w)
  (c3 : w ≤ 1)
  (c4 : 0 ≤ v)
solution
  (v := if |x| ≤ 1 then 0 else |x| - 1)
  (w := if |x| ≤ 1 then |x| else 1)
solutionEqualsAtom by
  simp [huber]
  split_ifs <;> ring
feasibility
  (c1 : by
    split_ifs <;> linarith)
  (c2 : by
    split_ifs <;> norm_num)
  (c3 : by
    split_ifs <;> linarith)
  (c4 : by
    split_ifs <;> linarith)
optimality by
  simp [huber]
  split_ifs with h
  { by_cases hwx : w ≤ |x|
    { have hsq : |x| ^ 2 - w ^ 2 = (|x| + w) * (|x| - w) := by ring_nf; simp
      rw [←sub_le_iff_le_add, ←sq_abs, ←rpow_two, ←rpow_two, hsq]
      apply mul_le_mul <;> linarith }
    { replace hwx := not_le.mp hwx
      by_cases hxz : x = 0
      { simp [hxz]
        apply add_nonneg <;> norm_num [c2, c4] }
      have hcx : 0 < |x| := abs_pos.mpr hxz
      have hx2w2 := mul_lt_mul hwx (le_of_lt hwx) hcx c2
      rw [←pow_two, sq_abs, ←pow_two] at hx2w2
      have hv : 0 ≤ 2 * v := by linarith
      have hx2w22v := add_le_add (le_of_lt hx2w2) hv
      linarith } }
  { have h2xsub1 : 2 * |x| - 1  ≤ 2 * v + (2 * w - 1) := by linarith
    apply le_trans h2xsub1
    apply add_le_add (le_refl _)
    rw [←zero_add (_ - _), ←le_sub_iff_add_le]
    have hwsub12 : w * w - (2 * w - 1) = (w - 1) * (w - 1) := by ring_nf
    rw [pow_two, hwsub12]
    exact mul_self_nonneg _ }
vconditionElimination

declare_atom Vec.huber [convex] (m : Nat)& (x : Fin m → ℝ)? : Vec.huber x :=
vconditions
implementationVars (v : Fin m → ℝ) (w : Fin m → ℝ)
implementationObjective (2 • v + w ^ 2)
implementationConstraints
  (c1 : |x| ≤ v + w)
  (c2 : 0 ≤ w)
  (c3 : w ≤ 1)
  (c4 : 0 ≤ v)
solution
  (v := fun i => if |x i| ≤ 1 then 0 else |x i| - 1)
  (w := fun i => if |x i| ≤ 1 then |x i| else 1)
solutionEqualsAtom by
  ext i
  simp [Vec.huber, ←huber.solEqAtom (x i)]
feasibility
  (c1 : by
    simpa using (fun i => huber.feasibility0 (x i)))
  (c2 : by
    simpa using (fun i => huber.feasibility1 (x i)))
  (c3 : by
    simpa using (fun i => huber.feasibility2 (x i)))
  (c4 : by
    simpa using (fun i => huber.feasibility3 (x i)))
optimality by
    intros i
    simp [Vec.huber]
    have := huber.optimality (x i) (v i) (w i) (c1 i) (c2 i) (c3 i) (c4 i)
    convert this
    simp
vconditionElimination

end CvxLean
