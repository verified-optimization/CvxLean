import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CvxLean.Lib.Math.Data.Real

/-!
We follow the MOSEK modeling cookbook:
https://docs.mosek.com/modeling-cookbook/cqo.html
-/

namespace Real

open BigOperators

variable {n m} [Fintype m] [Fintype n]

/-- The `n`-dimensional second-order cone
      `𝒬ⁿ⁺¹ := { (t, x) | ‖x‖₂ = sqrt(x₁² + ⋯ + xₙ²) ≤ t } ⊆ ℝ × ℝⁿ`. -/
def soCone (t : ℝ) (x : n → ℝ) : Prop :=
  sqrt (∑ i, x i ^ 2) ≤ t

/-- The `n`-dimensional rotated second-order cone
      `𝒬ᵣⁿ⁺² := { (v, w, x) | x₁² + ⋯ + xₙ² ≤ 2vw ∧ 0 ≤ v, w } ⊆ ℝ × ℝ × ℝⁿ`. -/
def rotatedSoCone (v w : ℝ) (x : n → ℝ) : Prop :=
  (∑ i, x i ^ 2) ≤ (v * w) * 2 ∧ 0 ≤ v ∧ 0 ≤ w

/-- `m` copies of the `n`-dimensional second-order cone `(𝒬ⁿ)ᵐ`. -/
def Vec.soCone (t : m → ℝ) (X : Matrix m n ℝ) : Prop :=
  ∀ i, Real.soCone (t i) (X i)

/-- `m` copies of the `n`-dimensional rotated second-order cone `(𝒬ᵣⁿ)ᵐ`. -/
def Vec.rotatedSoCone (v w : m → ℝ) (X : Matrix m n ℝ) : Prop :=
  ∀ i, Real.rotatedSoCone (v i) (w i) (X i)

noncomputable section ConeConversion

/-- If `(t, x) ∈ 𝒬ⁿ⁺¹` then `r(t, x) ∈ 𝒬ᵣⁿ⁺²`. -/
def rotateSoCone {n : ℕ} (t : ℝ) (x : Fin n.succ → ℝ) : ℝ × ℝ × (Fin n → ℝ) :=
  ((t + x 0) / sqrt 2, (t - x 0) / sqrt 2, fun i => x i.succ)

lemma rotateSoCone_rotatedSoCone {n : ℕ} {t : ℝ} {x : Fin n.succ → ℝ}
  (h : soCone t x) :
  let (v, w, x) := rotateSoCone t x; rotatedSoCone v w x := by
  simp [rotatedSoCone, rotateSoCone]
  have habsx0t : |x 0| ≤ t := by
    rw [soCone, Fin.sum_univ_succ] at h
    have hS : 0 ≤ ∑ i : Fin n, x (Fin.succ i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact abs_le_of_sqrt_sq_add_nonneg_le hS h
  have ht : 0 ≤ t := le_trans (abs_nonneg _) habsx0t
  replace ⟨hx0t, hnx0t⟩ := abs_le.mp habsx0t
  split_ands
  { field_simp
    have hrw : (t + x 0) * (t - x 0) = t ^ 2 - x 0 ^ 2 := by ring
    rw [hrw, le_sub_iff_add_le, add_comm]
    rw [←Fin.sum_univ_succ (f := fun i => (x i) ^ 2)]
    rw [←sqrt_le_left ht]
    exact h }
  { simp [le_div_iff]; linarith }
  { simp [le_div_iff]; linarith }

/-- If `(v, w, x) ∈ 𝒬ⁿ⁺²` then `u(v, w, x) ∈ 𝒬ᵣⁿ⁺¹`. -/
def unrotateSoCone {n : ℕ} (v w : Real) (x : Fin n → ℝ) :
  ℝ × (Fin n.succ → ℝ) :=
  ((v + w) / sqrt 2, Matrix.vecCons ((v - w) / sqrt 2) x)

lemma unrotateSoCone_soCone {n : ℕ} {v w : ℝ} {x : Fin n → ℝ}
  (h : rotatedSoCone v w x) :
  let (t, x) := unrotateSoCone v w x; soCone t x := by
  simp [soCone, unrotateSoCone]
  replace ⟨h, hv, hw⟩ := h
  rw [sqrt_le_iff]
  split_ands
  { simp [le_div_iff]; linarith }
  { rw [Fin.sum_univ_succ]
    simp [Matrix.vecCons]
    rw [add_comm, ←le_sub_iff_add_le]
    field_simp
    have hrw : ((v + w) ^ 2 - (v - w) ^ 2) / 2 = v * w * 2 := by ring
    rwa [hrw] }

-- TODO(RFM): rotate then unrotate?
-- TODO(RFM): unrotate then rotate?

end ConeConversion

section Lemmas

/-- To handle powers, a common trick is to use the fact that for
`x, y ≥ 0` and `z ∈ ℝ`,
      `((x + y), (x - y, 2z)ᵀ) ∈ 𝒬ⁿ⁺¹ ↔ z ^ 2 ≤ xy`. -/
lemma soCone_add_sub_two_mul_of_nonneg {x y : ℝ} (z : ℝ)
  (hx : 0 ≤ x) (hy : 0 ≤ y) :
  soCone (x + y) ![x - y, 2 * z] ↔ z ^ (2 : ℝ) ≤ x * y := by
  have hxy := add_nonneg hx hy
  conv => lhs; unfold soCone; simp [sqrt_le_left hxy, ←le_sub_iff_add_le']
  ring_nf; simp

/-- Same as `soCone_add_sub_two_mul_of_nonneg` with `z = 1`. -/
lemma soCone_add_sub_two_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  soCone (x + y) ![x - y, 2] ↔ 1 ≤ x * y := by
  have h := soCone_add_sub_two_mul_of_nonneg 1 hx hy
  rw [mul_one, one_rpow] at h
  exact h

/-- Same as `soCone_add_sub_two_mul_of_nonneg` replacing `y` by `-y`. -/
lemma soCone_sub_add_two_mul_of_nonneg {x y : ℝ} (z : ℝ) :
  soCone (x - y) ![x + y, 2 * z] ↔ y ≤ x ∧ z ^ (2 : ℝ) ≤ -(x * y) := by
  conv => lhs; unfold soCone; simp [sqrt_le_iff, ←le_sub_iff_add_le']
  apply Iff.and
  { rfl }
  { ring_nf!; rw [←neg_mul, ←div_le_iff (by norm_num)]; simp }

end Lemmas

end Real
