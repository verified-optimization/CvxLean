import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real

noncomputable def entr (x : Real) :=
  -(x * Real.log x)

noncomputable def huber (x : Real) :=
  if abs x ≤ 1 then x ^ 2 else 2 * abs x - 1

noncomputable def klDiv (x y : Real) :=
  x * log (x / y) - x + y

/- Lemmas used in `RewriteMapLibrary`. -/
section Lemmas

lemma Real.log_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x = Real.log y ↔ x = y :=
  ⟨fun h => by
    have hxmem := Set.mem_Ioi.2 hx
    have hymem := Set.mem_Ioi.2 hy
    have heq : Set.restrict (Set.Ioi 0) log ⟨x, hxmem⟩ =
      Set.restrict (Set.Ioi 0) log ⟨y, hymem⟩ := by
      simp [h]
    have h := Real.log_injOn_pos.injective heq
    simp [Subtype.eq] at h
    exact h,
  fun h => by rw [h]⟩

lemma Real.div_pow_eq_mul_pow_neg {a b c : ℝ} (hb : 0 ≤ b) : a / (b ^ c) = a * b ^ (-c) := by
  rw [div_eq_mul_inv, ←rpow_neg hb]

lemma Real.one_div_eq_pow_neg_one {a : ℝ} (ha : 0 < a) : 1 / a = a ^ (-1) := by
  rw [Real.rpow_neg (le_of_lt ha), rpow_one, div_eq_mul_inv, one_mul]

lemma Real.inv_eq_pow_neg_one {a : ℝ} (ha : 0 < a) : a⁻¹ = a ^ (-1) := by
  rw [inv_eq_one_div, Real.one_div_eq_pow_neg_one ha]

lemma Real.pow_half_two {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2)) ^ 2 = x := by
  show Real.rpow (Real.rpow _ _) _ = _
  rw [rpow_eq_pow, rpow_eq_pow, ← rpow_mul hx]
  norm_num

lemma Real.binomial_two (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + (2 * (x * y) + y ^ 2) := by
  simp only [rpow_two]; ring

lemma Real.exp_neg_eq_one_div (x : ℝ) : exp (-x) = 1 / exp x := by
  rw [exp_neg, inv_eq_one_div]

end Lemmas

end Real
