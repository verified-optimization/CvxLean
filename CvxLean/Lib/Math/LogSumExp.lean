import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec

namespace Vec

open Real

lemma sum_exp_eq_sum_div (x : Fin n → ℝ) (t : ℝ) :
  Vec.sum (Vec.exp (x - Vec.const n t)) = (Vec.sum (Vec.exp x)) / (Real.exp t) := by
  unfold Vec.sum
  rw [Finset.sum_div]
  congr; ext i
  simp [Vec.exp, Vec.const, Real.exp_sub]

lemma sum_exp_pos {n} (hn : 0 < n) (x : Fin n → ℝ) :
  0 < Vec.sum (Vec.exp x) := by
  apply Finset.sum_pos
  { intros i _; simp [Vec.exp, Real.exp_pos] }
  { existsi ⟨0, hn⟩; simp }

end Vec
