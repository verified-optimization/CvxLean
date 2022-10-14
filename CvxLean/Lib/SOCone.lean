import Mathbin.Data.Real.Sqrt
import Mathbin.Data.Matrix.Basic
import CvxLean.Lib.Missing.Mathlib
import CvxLean.Lib.Missing.Vec

/- 
https://docs.mosek.com/modeling-cookbook/cqo.html#sec-cqo-rquadcone

This file defines the second-order cone.
-/

namespace Real

variable [Fintype m] [Fintype n]

def soCone (t : ℝ) (x : n → ℝ) : Prop :=
  sqrt (∑ i, x i ^ 2) ≤ t

def rotatedSoCone (v w : ℝ) (x : n → ℝ) : Prop :=
  (∑ i, x i ^ 2) ≤ (v * w) * 2 ∧ 0 ≤ v ∧ 0 ≤ w

section SOConeLemmas

variable (t v w : ℝ) (x : n → ℝ)

noncomputable def rotateSoCone {n : ℕ} (t : ℝ) (x : Finₓ n.succ → ℝ) : 
  ℝ × ℝ × (Finₓ n → ℝ) :=
  ((t + x 0) / sqrt 2, (t - x 0) / sqrt 2, fun i => x i.succ)

noncomputable def unrotateSoCone {n : ℕ} (v w : ℝ) (x : Finₓ n → ℝ) : 
   ℝ × (Finₓ n.succ → ℝ) :=
((v + w) / sqrt 2, Matrix.vecCons ((v - w) / sqrt 2) x)

end SOConeLemmas

namespace Vec

variable [Fintype m] [Fintype n]

def soCone (t : m → ℝ) (X : Matrix m n ℝ) : Prop :=
  ∀ i, Real.soCone (t i) (X i)

def rotatedSoCone (v w : m → ℝ) (X : Matrix m n ℝ) : Prop :=
  ∀ i, Real.rotatedSoCone (v i) (w i) (X i)

end Vec

end Real
