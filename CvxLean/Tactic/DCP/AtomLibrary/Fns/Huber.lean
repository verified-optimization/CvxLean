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

-- def huberF (x : Float) : Float :=
-- if x.abs ≤ 1 then x^2 else 2*x.abs - 1

-- def vW (x : Float) : Float :=
-- if x.abs ≤ 1 then 0 else x.abs - 1

-- def vV (x : Float) : Float :=
-- if x.abs ≤ 1 then x else 1

-- #eval (huberF 8) - (2 * (vW 8) + (vV 8)^2)
-- #eval (huberF 0.1) - (2 * (vW 0.1) + (vV 0.1)^2)

-- #eval 8 ≤ (vW 8) + (vV 8)
-- #eval 8 ≤ (vW (-8)) + (vV (-8))
-- #eval 0.1 ≤ (vW 0.1) + (vV 0.1)
-- #eval 0.1 ≤ (vW (-0.1)) + (vV (-0.1))

declare_atom huber1 [convex] (x : ℝ)? : huber x 1 :=
vconditions
implementationVars (v : ℝ) (w : ℝ) -- (z : ℝ)
implementationObjective (2 * v + w ^ 2)
implementationConstraints
  -- (c1 : rotatedSoCone z (1/2) ![w])
  (c2 : |x| ≤ v + w)
  (c3 : w ≤ 1)
  (c4 : 0 ≤ v)
solution
  -- (v := if |x| ≤ 1 then 0 else |x| - 1)
  -- (w := if |x| ≤ 1 then |x| else 1)
  (v := if |x| ≤ 1 then 0 else |x| - 1)
  (w := if |x| ≤ 1 then |x| else 1)
  -- (z := if |x| ≤ 1 then x ^ 2 else 1)
solutionEqualsAtom by
  simp [huber]
  split_ifs <;> ring
feasibility
  -- (c1 : sorry)
  (c2 : by
    split_ifs <;> linarith)
  (c3 : by
    split_ifs <;> linarith)
  (c4 : by
    split_ifs <;> linarith)
optimality by
  -- intros y hy
  simp [huber]
  split_ifs with h
  { have hx : 0 ≤ x := sorry
  
    -- rw [←abs_eq_self.mpr (le_of_lt one_pos)] at h
    -- replace h := sq_le_sq.mpr h
    -- apply le_trans h
    -- simp
    -- have hvw := le_trans (abs_nonneg _) c2
    -- rw [abs_le] at c2
    -- rw [←abs_eq_self.mpr hvw] at c2
    -- replace c2 := sq_le_sq.mpr c2
    -- apply le_trans c2
    -- simp [rotatedSoCone] at c1
   }
  { sorry }
vconditionElimination

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
