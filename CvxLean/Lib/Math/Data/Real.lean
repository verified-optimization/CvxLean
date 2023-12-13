import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real

/- New named functions. Each corresponds to an atom. -/
section Functions

noncomputable def entr (x : Real) :=
  -(x * log x)

noncomputable def huber (x : Real) :=
  if abs x ≤ 1 then x ^ 2 else 2 * abs x - 1

noncomputable def klDiv (x y : Real) :=
  x * log (x / y) - x + y

end Functions

/- Useful to construct expressions, as otherwise they are derived from other
instances. -/
section Instances

noncomputable instance instDivReal : Div ℝ := by
  infer_instance

noncomputable instance instAbsReal : Abs ℝ := by
  infer_instance

noncomputable instance instMinReal : Min ℝ := by
  infer_instance

noncomputable instance instMaxReal : Max ℝ := by
  infer_instance

end Instances

/- Lemmas used in `RewriteMapLibrary`. -/
section Lemmas

lemma log_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  log x = log y ↔ x = y :=
  ⟨fun h => by
    have hxmem := Set.mem_Ioi.2 hx
    have hymem := Set.mem_Ioi.2 hy
    have heq : Set.restrict (Set.Ioi 0) log ⟨x, hxmem⟩ =
      Set.restrict (Set.Ioi 0) log ⟨y, hymem⟩ := by
      simp [h]
    have h := log_injOn_pos.injective heq
    simp [Subtype.eq] at h
    exact h,
  fun h => by rw [h]⟩

lemma div_pow_eq_mul_pow_neg {a b c : ℝ} (hb : 0 ≤ b) :
  a / (b ^ c) = a * b ^ (-c) := by
  rw [div_eq_mul_inv, ←rpow_neg hb]

lemma one_div_eq_pow_neg_one {a : ℝ} (ha : 0 < a) : 1 / a = a ^ (-1) := by
  rw [rpow_neg (le_of_lt ha), rpow_one, div_eq_mul_inv, one_mul]

lemma inv_eq_pow_neg_one {a : ℝ} (ha : 0 < a) : a⁻¹ = a ^ (-1) := by
  rw [inv_eq_one_div, one_div_eq_pow_neg_one ha]

lemma pow_half_two {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2)) ^ 2 = x := by
  show rpow (rpow _ _) _ = _
  rw [rpow_eq_pow, rpow_eq_pow, ← rpow_mul hx]
  norm_num

lemma pow_two_le_pow_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  x ^ 2 ≤ y ^ 2 ↔ x ≤ y := by
  rw [rpow_two, rpow_two, sq_le_sq, abs_of_nonneg hx, abs_of_nonneg hy]

lemma binomial_two (x y : ℝ) :
  (x + y) ^ 2 = x ^ 2 + (2 * (x * y) + y ^ 2) := by
  simp only [rpow_two]; ring

lemma rpow_eq_mul_rpow_pred {x y : ℝ} (hx : x ≠ 0) :
  x ^ y = x * (x ^ (y - 1)) := by
  conv => left; rw [(by ring : y = (y - 1) + 1), rpow_add_one hx, mul_comm]

lemma exp_neg_eq_one_div (x : ℝ) : exp (-x) = 1 / exp x := by
  rw [exp_neg, inv_eq_one_div]

end Lemmas

end Real
