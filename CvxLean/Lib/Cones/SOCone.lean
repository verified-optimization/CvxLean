import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
https://docs.mosek.com/modeling-cookbook/cqo.html#sec-cqo-rquadcone

This file defines the second-order cone.
-/

namespace Real

open BigOperators

variable [Fintype m] [Fintype n]

def soCone (t : Real) (x : n → Real) : Prop :=
  sqrt (∑ i, x i ^ 2) ≤ t

def rotatedSoCone (v w : Real) (x : n → Real) : Prop :=
  (∑ i, x i ^ 2) ≤ (v * w) * 2 ∧ 0 ≤ v ∧ 0 ≤ w

def Vec.soCone (t : m → Real) (X : Matrix m n Real) : Prop :=
  ∀ i, Real.soCone (t i) (X i)

def Vec.rotatedSoCone (v w : m → Real) (X : Matrix m n Real) : Prop :=
  ∀ i, Real.rotatedSoCone (v i) (w i) (X i)

section ConeConversion

noncomputable def rotateSoCone {n : ℕ} (t : Real) (x : Fin n.succ → Real) :
  Real × Real × (Fin n → Real) :=
  ((t + x 0) / sqrt 2, (t - x 0) / sqrt 2, fun i => x i.succ)

noncomputable def unrotateSoCone {n : ℕ} (v w : Real) (x : Fin n → Real) :
   Real × (Fin n.succ → Real) :=
((v + w) / sqrt 2, Matrix.vecCons ((v - w) / sqrt 2) x)

end ConeConversion

section Lemmas

/-- To handle powers, a common trick is to consider for x, y ≥ 0, z ∈ ℝ,
      ((x + y), (x - y, 2 * z)^T) ∈ SO,
which is equivalent to z ^ 2 ≤ x * y. -/
lemma soCone_add_sub_two_mul_of_nonneg {x y : ℝ} (z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
  soCone (x + y) ![x - y, 2 * z] ↔ z ^ (2 : ℝ) ≤ x * y := by
  have hxy := add_nonneg hx hy
  conv => lhs; unfold soCone; simp [sqrt_le_left hxy, ←le_sub_iff_add_le']
  ring_nf; simp

lemma soCone_add_sub_two_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  soCone (x + y) ![x - y, 2] ↔ 1 ≤ x * y := by
  have h := soCone_add_sub_two_mul_of_nonneg 1 hx hy
  rw [mul_one, one_rpow] at h
  exact h

end Lemmas

end Real
