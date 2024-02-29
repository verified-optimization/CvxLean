import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Le
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sub
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

namespace CvxLean

open Real

-- TODO(RFM): same issue as in `quadOverLin`, no clear way to have 0 < y as a
-- vcondition, the exp y' ≤ y trick makes the solver stall.
declare_atom klDiv [convex] (x : ℝ)? (y : ℝ)? : x * log (x / y) - x + y  :=
vconditions
  (hx : 0 ≤ x)
  (hy : 1 / 100000 ≤ y)
implementationVars (t : ℝ)
implementationObjective (y - x - t)
implementationConstraints
  (c1 : expCone t x y)
  (c2 : 1 / 100000 ≤ y)
solution (t := -(x * log (x / y)))
solutionEqualsAtom by
  ring
feasibility
  (c1 : by
    dsimp
    unfold expCone
    cases (lt_or_eq_of_le hx) with
    | inl hx =>
        left
        refine ⟨hx, ?_⟩
        have hypos : 0 < y := by positivity
        rw [mul_comm _ (log _), ←neg_mul, ←mul_div, div_self (ne_of_gt hx)]
        rw [mul_one, exp_neg, exp_log (div_pos hx hypos), inv_div, mul_div]
        rw [div_le_iff hx, mul_comm]
    | inr hx =>
        replace hx := hx.symm
        right
        simp [hx]
        positivity)
  (c2 : by
      exact hy)
optimality by
  unfold expCone at c1
  cases c1 with
  | inl c =>
      have hxpos := c.1
      have hypos := lt_of_lt_of_le (mul_pos hxpos (exp_pos _)) c.2
      have hlhs : x * log (x / y) - x + y = x * log (x / y) + (y - x) := by ring
      conv => lhs; rw [hlhs]
      have hrhs : y - x - t = -t + (y - x) := by ring
      conv => rhs; rw [hrhs]
      apply add_le_add_right
      rw [mul_comm, ←le_div_iff c.1, neg_div]
      rw [←exp_le_exp, exp_log (div_pos hxpos hypos), exp_neg, ←inv_div]
      rw [inv_le_inv (div_pos hypos hxpos) (exp_pos _)]
      rw [le_div_iff hxpos, mul_comm]
      exact c.2
  | inr c =>
      simp [c.1, c.2.2]
vconditionElimination
  (hx : by
    unfold expCone at c1
    cases c1 with
    | inl c => exact le_of_lt c.1
    | inr c => rw [c.1])
  (hy : by
    exact c2)

declare_atom klDiv2 [convex] (x : ℝ)? (y : ℝ)? : klDiv x y :=
vconditions
  (hx : 0 ≤ x)
  (hy : 1 / 100000 ≤ y)
implementationVars (t : ℝ)
implementationObjective (y - x - t)
implementationConstraints
  (c1 : expCone t x y)
  (c2 : 1 / 100000 ≤ y)
solution (t := -(x * log (x / y)))
solutionEqualsAtom by
  unfold klDiv
  ring
feasibility
  (c1 : klDiv.feasibility0 x y hx hy)
  (c2 : by
    dsimp
    have h := klDiv.feasibility1 x y hx hy
    unfold posOrthCone at h
    simpa using h)
optimality by
  apply klDiv.optimality x y t c1
  { unfold posOrthCone expCone at *
    simpa using c2 }
vconditionElimination
  (hx : by
    apply klDiv.vcondElim0 x y t c1
    unfold posOrthCone at *
    simpa using c2)
  (hy : by
    apply klDiv.vcondElim1 x y t c1
    unfold posOrthCone expCone at *
    simpa using c2)

declare_atom Vec.klDiv [convex] (m : Nat)& (x : Fin m → ℝ)? (y : Fin m → ℝ)? :
  Vec.klDiv x y :=
vconditions
  (hx : 0 ≤ x)
  (hy : (fun _ => 1 / 100000) ≤ y)
implementationVars (t : Fin m → ℝ)
implementationObjective (y - x - t)
implementationConstraints
  (c1 : Vec.expCone t x y)
  (c2 : Vec.const m (1 / 100000) ≤ y)
solution (t := fun i => -((x i) * log ((x i) / (y i))))
solutionEqualsAtom by
  unfold Vec.klDiv klDiv; ext i; simp; ring
feasibility
  (c1 : by
    simp [Vec.klDiv, klDiv]
    unfold Vec.expCone
    intros i
    exact (klDiv.feasibility0 (x i) (y i) (hx i) (hy i)))
  (c2 : by
    simp [Vec.klDiv, klDiv]
    intros i
    have h := klDiv.feasibility1 (x i) (y i) (hx i) (hy i)
    unfold posOrthCone at h
    simpa [Vec.const] using h)
optimality fun i => by
    unfold Vec.expCone at c1
    apply klDiv.optimality (x i) (y i) (t i) (c1 i)
    unfold posOrthCone expCone at *
    simpa [Vec.const] using (c2 i)
vconditionElimination
  (hx : fun i => by
    unfold Vec.expCone at c1
    apply klDiv.vcondElim0 (x i) (y i) (t i) (c1 i)
    unfold posOrthCone expCone at *
    simpa [Vec.const] using (c2 i))
  (hy : fun i => by
    unfold Vec.expCone at c1
    apply klDiv.vcondElim1 (x i) (y i) (t i) (c1 i)
    unfold posOrthCone expCone at *
    simpa [Vec.const] using (c2 i))

end CvxLean
