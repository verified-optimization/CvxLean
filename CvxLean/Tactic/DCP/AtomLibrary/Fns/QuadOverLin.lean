import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Add
import CvxLean.Tactic.DCP.AtomLibrary.Fns.SMul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Mul
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Transpose
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

-- TODO(RFM): generalize to x : Fin n → ℝ
-- TODO(RFM): distinguish between nonincreasing and nondecreasing.
declare_atom quadOverLin [convex] (x : ℝ)? (y : ℝ)- : x ^ (2 : ℝ) / y :=
vconditions
  (hy : 1 / 100000 ≤ y)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : soCone (y + t) ![y - t, 2 * x])
  (c2 : 0 ≤ t)
  (c3 : 1 / 100000 ≤ y)
solution (t := x ^ (2 : ℝ) / y)
solutionEqualsAtom by rfl
feasibility
  (c1 : by
    have hypos : 0 < y := by positivity
    have hynn : 0 ≤ y := by linarith
    have hx2ynn : 0 ≤ x ^ (2 : ℝ) / y := by
      rw [rpow_two]; exact div_nonneg (pow_two_nonneg x) hynn
    rw [soCone_add_sub_two_mul_of_nonneg _ hynn hx2ynn]
    rw [mul_div, mul_comm, ←mul_div, div_self (ne_of_gt hypos), mul_one])
  (c2 : by
    have hynn : 0 ≤ y := by positivity
    rw [rpow_two]
    exact div_nonneg (pow_two_nonneg x) hynn)
  (c3 : by
    exact hy)
optimality by
  intros z hyz
  have hy : 0 < y := by positivity
  have hynn := le_of_lt hy
  rw [soCone_add_sub_two_mul_of_nonneg x hynn c2] at c1
  have hz := lt_of_lt_of_le hy hyz
  rw [div_le_iff' hz]
  apply le_trans c1
  apply mul_le_mul hyz (le_refl _) c2 (le_of_lt hz)
vconditionElimination
  (hy : by
    intros z hz
    linarith)

open Matrix

-- TODO: Generalize to any fintype `m`.
declare_atom Vec.quadOverLin [convex] (n : ℕ)& (x : Fin n → ℝ)? (y : Fin n → ℝ)- :
    x ^ (2 : ℝ) / y :=
vconditions
  (hy : 1 / 100000 ≤ y)
implementationVars (t : Fin n → ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : Vec.soCone (y + t) ![y - t, 2 • x]ᵀ)
  (c2 : 0 ≤ t)
  (c3 : 1 / 100000 ≤ y)
solution (t := x ^ (2 : ℝ) / y)
solutionEqualsAtom by rfl
feasibility
  (c1 : by
    have hypos : StrongLT 0 y := fun i => by
      have hyi := hy i
      simp at hyi; positivity
    have hynn : 0 ≤ y := le_of_strongLT hypos
    have hx2ynn : 0 ≤ x ^ (2 : ℝ) / y := by
      intros i; dsimp
      rw [rpow_two]; exact div_nonneg (pow_two_nonneg (x i)) (hynn i)
    intros t i;
    have h_suff : soCone (y i + t i) (![y i - t i, 2 * x i]) := by
      rw [soCone_add_sub_two_mul_of_nonneg _ (hynn i) (hx2ynn i)]; dsimp
      rw [mul_div, mul_comm, ←mul_div, div_self (ne_of_gt (hypos i)), mul_one]
    convert h_suff; funext j; fin_cases j <;> simp)
  (c2 : by
    have hynn : 0 ≤ y := fun i => by
      have hyi := hy i
      simp at hyi; positivity
    intros t i; dsimp;
    rw [rpow_two]
    exact div_nonneg (pow_two_nonneg (x i)) (hynn i))
  (c3 : by
    exact hy)
optimality by
  intros z hyz
  have hy : StrongLT 0 y := fun i => by
    have hyzi := hyz i
    have c3i := c3 i
    simp at hyzi c3i; positivity
  have hynn : 0 ≤ y := le_of_strongLT hy
  intros i; dsimp
  have c1i := c1 i
  replace c1i : soCone (y i + t i) (![y i - t i, 2 * x i]) := by
    convert c1i; funext j; fin_cases j <;> simp
  rw [soCone_add_sub_two_mul_of_nonneg (x i) (hynn i) (c2 i)] at c1i
  have hz := lt_of_lt_of_le (hy i) (hyz i)
  rw [div_le_iff' hz]
  apply le_trans c1i
  apply mul_le_mul (hyz i) (le_refl _) (c2 i) (le_of_lt hz)
vconditionElimination
  (hy : by
    intros z hz i
    have hzi := hz i
    have c3i := c3 i
    linarith)

end CvxLean
