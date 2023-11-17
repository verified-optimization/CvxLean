import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Eq
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sq
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Abs
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

set_option trace.Meta.debug true in
declare_atom huber1 [convex] (x : ℝ)+ (M : ℝ)& : huber x M :=
bconditions
  (hM : 0 ≤ M)
vconditions
  (hx : 0 ≤ x)
implementationVars (n : ℝ) (s : ℝ)
implementationObjective (n ^ 2 + 2 * s)
implementationConstraints
  (c1 : 0 ≤ s)
  (c2 : x = s + n)
solution
  (n := if |x| ≤ M then 2 * M - x else M)
  (s := if |x| ≤ M then 2 * x - 2 * M else x - M)
solutionEqualsAtom by
  simp [huber]
  split_ifs
  { field_simp

  }
  . sorry
feasibility
  (c1 : sorry)
  (c2 : sorry)
  (c3 : sorry)
optimality by
  sorry
vconditionElimination
  (hx : by
    sorry)

-- declare_atom Vec.klDiv [convex] (m : Nat)& (x : Fin m → ℝ)? (y : Fin m → ℝ)? :
--   Vec.klDiv x y :=
-- vconditions
--   (hx : 0 ≤ x)
--   (hy : ∀ i, 0 < y i)
-- implementationVars (t : Fin m → ℝ) (y' : Fin m → ℝ)
-- implementationObjective (y - x - t)
-- implementationConstraints
--   (c1 : Vec.expCone t x y)
--   (c2 : Vec.exp y' ≤ y)
-- solution (t := fun i => -((x i) * log ((x i) / (y i)))) (y' := Vec.log y)
-- solutionEqualsAtom by
--   simp [Vec.klDiv, klDiv]; ext i; simp; ring
-- feasibility
--   (c1 : by
--     simp [Vec.klDiv, klDiv]
--     intros i
--     exact (klDiv.feasibility0 (x i) (y i) (hx i) (hy i)))
--   (c2 : by
--     simp [Vec.klDiv, klDiv]
--     intros i
--     exact klDiv.feasibility1 (x i) (y i) (hx i) (hy i))
-- optimality by
--     simp [Vec.klDiv, klDiv]
--     intros i
--     exact klDiv.optimality (x i) (y i) (t i) (y' i) (c1 i) (c2 i)
-- vconditionElimination
--   (hx : fun i => klDiv.vcondElim0 (x i) (y i) (t i) (y' i) (c1 i) (c2 i))
--   (hy : fun i => klDiv.vcondElim1 (x i) (y i) (t i) (y' i) (c1 i) (c2 i))

end CvxLean
