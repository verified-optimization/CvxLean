-- import CvxLean.Tactic.DCP.Atoms
-- import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
-- import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
-- import CvxLean.Tactic.DCP.AtomLibrary.Sets.Eq
-- import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sq
-- import CvxLean.Tactic.DCP.AtomLibrary.Fns.Abs
-- import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
-- import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

import CvxLean.Command.Solve

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

#check instSupReal

#check Sup.sup

addRealToFloat : instSupReal := Sup.mk (fun (x y : Float) => if x ≤ y then y else x)

noncomputable def prob := let x := -0.1;
  optimization (v : ℝ) (w : ℝ)
    minimize (2 * v + w ^ 2)
    subject to
      c1 : abs x ≤ v + w
      c2 : w ≤ 1
      c3 : 0 ≤ v

solve prob

#eval prob.solution

#check sub_le_iff_le_add

-- (set-logic ALL)
-- (set-option :produce-models true)
-- (declare-fun x () Real)
-- (declare-fun v () Real)
-- (declare-fun w () Real)

-- (assert (<= (abs x) 1))
-- (assert (<= (abs x) (+ v w)))
-- (assert (<= 0 w))
-- (assert (<= w 1))
-- (assert (<= 0 v))
-- (assert (not (<= (^ x 2) (+ (* 2 v) (^ w 2)))))

-- (check-sat)
-- (get-proof)

-- #find _ ^ _ - _ = _

declare_atom huber1 [convex] (x : ℝ)? : huber x 1 :=
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
  { by_cases hca : w ≤ |x|
    {
      rw [←sub_le_iff_le_add]
      have : |x| ^ 2 - w ^ 2 = (|x| + w) * (|x| - w) := by ring_nf; simp
      rw [←sq_abs]
      rw [←rpow_two, ←rpow_two, this]
      apply mul_le_mul
      { linarith }
      { linarith }
      { linarith }
      { norm_num }
    }
    {
      replace hca := not_le.mp hca
      by_cases hxz : x = 0
      {
        rw [hxz]
        simp
        apply add_nonneg <;> norm_num [c2, c4]
      }
      have hcx : 0 < |x| := abs_pos.mpr hxz
      have hx2 := mul_lt_mul hca (le_of_lt hca) hcx c2
      rw [←pow_two, sq_abs, ←pow_two] at hx2
      have hv : 0 ≤ 2 * v := by linarith
      have := add_le_add (le_of_lt hx2) hv
      linarith
    }
   }
  { sorry }
vconditionElimination

#check abs

-- noncomputable def prob := let x := -1.5;
--   optimization (t : ℝ) (t₁ : ℝ) (t₂ : ℝ) (t₃ : ℝ) (x₁ : ℝ) (x₂ : ℝ) (x₃ : ℝ)
--     minimize (t)
--     subject to
--       c1 : t₁ + t₂ + t₃ - 2 ≤ t
--       c2 : x = x₁ + x₂ + x₃
--       c3 : t₁ = -2 * x₁ - 1
--       c4 : x₂ ^ 2 ≤ t₂
--       c5 : t₃ = 2 * x₃ - 1
--       c6 : x₁ ≤ -1
--       c7 : -1 ≤ x₂
--       c8 : x₂ ≤ 1
--       c9 : 1 ≤ x₃

-- solve prob

-- #eval prob.solution

#check abs_eq_neg_self.mpr

noncomputable def huber' (x : ℝ) : ℝ :=
if x ≤ -1 then
  -2 * x - 1
else
  if x ≤ 1 then
    x ^ 2
  else
    2 * x - 1

declare_atom huber2 [convex] (x : ℝ)? : huber' x :=
vconditions
implementationVars (t : ℝ) (t₁ : ℝ) (t₂ : ℝ) (t₃ : ℝ) (x₁ : ℝ) (x₂ : ℝ) (x₃ : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : t₁ + t₂ + t₃ - 2 ≤ t)
  (c2 : x = x₁ + x₂ + x₃)
  (c3 : t₁ = -2 * x₁ - 1)
  (c4 : x₂ ^ 2 ≤ t₂)
  (c5 : t₃ = 2 * x₃ - 1)
  (c6 : x₁ ≤ -1)
  (c7 : -1 ≤ x₂)
  (c8 : x₂ ≤ 1)
  (c9 : 1 ≤ x₃)
solution
  (t := huber' x)
  (t₁ := if x ≤ -1 then -2 * x - 1 else 1)
  (t₂ := if -1 ≤ x then (if x ≤ 1 then x ^ 2 else 1) else 1)
  (t₃ := if 1 ≤ x then 2 * x - 1 else 1)
  (x₁ := if x ≤ -1 then x else -1)
  (x₂ := if -1 ≤ x then (if x ≤ 1 then x else 1) else -1)
  (x₃ := if 1 ≤ x then x else 1)
solutionEqualsAtom by
  rfl
feasibility
  (c1 : by
    simp [huber']
    split_ifs with h1 h2 h3 h4 <;>
    try { linarith }
    ring_nf
    simp [neg_mul, abs_le, h2, h3])
  (c2 : by
    simp [huber']
    split_ifs <;> linarith)
  (c3 : by
    simp [huber]
    split_ifs <;> norm_num)
  (c4 : by
    simp [huber])
  (c5 : by
    simp [huber]
    split_ifs <;> norm_num <;> linarith)
  (c6 : by
    simp [huber]
    split_ifs <;> linarith)
  (c7 : by
    simp [huber]
    split_ifs <;> linarith)
  (c8 : by
    simp [huber]
    split_ifs <;> linarith)
  (c9 : by
    simp [huber]
    split_ifs <;> linarith)
optimality by
  simp [huber']
  split_ifs with h
  { have ht₂ : 0 ≤ t₂ := sorry
    have h1 : - (2 * x) - 1 ≤ t₁ + t₂ + t₃ - 2 := by
      rw [c2, c3, c5]
      have : -2 * x₁ - 1 + (2 * x₃ - 1) - 2 ≤ -2 * x₁ - 1 + t₂ + (2 * x₃ - 1) - 2 :=
        by linarith
      refine le_trans ?_ this
      calc
        -(2 * (x₁ + x₂ + x₃)) - 1
          = -2 * x₁ - 1 -(2 * x₂) + -(2 * x₃) := by ring
        _ ≤ -2 * x₁ - 1 + 2 + -(2 * x₃) := by linarith
        _ ≤ -2 * x₁ - 1 + 2 * x₃ - 3 := by sorry
        _ = -2 * x₁ - 1 + (2 * x₃ - 1) - 2 := by ring
    exact le_trans h1 c1
   }
  { sorry }
  { replace h := lt_of_not_le h
    sorry }
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
