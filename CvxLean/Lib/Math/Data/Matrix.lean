import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Array.Defs

import CvxLean.Lib.Math.Data.List

namespace Matrix

instance [Preorder α] : Preorder (Matrix m n α) :=
{ le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_refl _
  le_trans := fun _ _ _ hAB hBC i j => le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _ }

def abs (A : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => Abs.abs (A i j)

instance : Abs (Matrix m n ℝ) := ⟨abs⟩

theorem vecCons_zero_zero {n}
  : vecCons (0 : ℝ) (0 : Fin n → ℝ) = 0 := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

theorem smul_vecCons {n} (x : ℝ) (y : ℝ) (v : Fin n → ℝ)
  : x • vecCons y v = vecCons (x • y) (x • v) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

theorem add_vecCons {n} (x : ℝ) (v : Fin n → ℝ) (y : ℝ) (w : Fin n → ℝ)
  : vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

open BigOperators

def sum [Fintype m] [AddCommMonoid α] (X : Matrix m m α) : α :=
  ∑ i, (∑ j, X i j)

-- Transform to arrays to compute.
namespace Computable

variable {α} [Zero α]

@[to_additive "See also `add_monoid.to_add_action`"]
instance (priority := 910) Mul.toHasSmul' (α : Type _) [Mul α] : SMul α α :=
  ⟨(· * ·)⟩

def vecToArray (v : Fin n → α) : Array α :=
  (Array.range n).map (fun i => if h : @LT.lt ℕ instLTNat i n then v ⟨i, h⟩ else 0)

def toArray (M : Matrix (Fin n) (Fin n) α) : Array (Array α) :=
  (vecToArray M).map vecToArray

def dotProduct [Mul α] [Add α] (v w : Fin n → α) : α :=
  ((Array.zip (vecToArray v) (vecToArray w)).map (fun ⟨a, b⟩ => a * b)).foldl (· + ·) 0

infixl:72 " ⬝ᵥᶜ " => Matrix.Computable.dotProduct

def mulVec [Mul α] [Add α] (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : Fin m → α
  | i => (fun j => M i j) ⬝ᵥᶜ v

def vecMul [Mul α] [Add α] (v : (Fin m) → α) (M : Matrix (Fin m) (Fin n) α) : Fin n → α
  | j => v ⬝ᵥᶜ fun i => M i j

def transpose (α) (M : Matrix m n α) : Matrix n m α
  | x, y => M y x

def diag (α) (M : Matrix n n α) : n → α
  | x => M x x

def mul [Mul α] [Add α] (M : Matrix (Fin l) (Fin m) α) (N : Matrix (Fin m) (Fin n) α) : Matrix (Fin l) (Fin n) α :=
fun i k => (fun j => M i j) ⬝ᵥᶜ (fun j => N j k)

infixl:75 " ⬝ᶜ " => Matrix.Computable.mul

def tr [Add α] (A : Matrix (Fin n) (Fin n) α) : α :=
  (Computable.vecToArray (fun i => A i i)).foldl (· + ·) 0

def PosDef [Add α] [Mul α] [LT α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ x : (Fin n) → α, Matrix.Computable.vecMul x A ⬝ᵥᶜ x > 0

def PosSemidef [Add α] [Mul α] [LE α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ x : (Fin n) → α, Matrix.Computable.vecMul x A ⬝ᵥᶜ x ≥ 0

def posDefObjective [Add α] [Mul α] (C X : Matrix (Fin n) (Fin n) α) : α :=
  Matrix.Computable.tr (Matrix.Computable.mul C X)

def quadForm [Add α] [Mul α] (A : Matrix (Fin n) (Fin n) α) (x : (Fin n) → α) :=
  Matrix.Computable.vecMul x A ⬝ᵥᶜ x

def covarianceMatrix [Add α] [Mul α] [Div α] {N n : ℕ} [OfNat α N] (Y : Matrix (Fin N) (Fin n) α) (i j : Fin n) :=
  ((Computable.vecToArray Y).map (fun y => (y i) * y j)).foldl (· + ·) 0 / (OfNat.ofNat N)

def diagonal {n : Type u_3} {α : Type v} [DecidableEq n] [Zero α] (x : n → α) : Matrix n n α :=
  fun i j => (if i = j then x i else 0)

def fromBlocks {l : Type}
  {m : Type} {n : Type} {o : Type} {α : Type}
  : Matrix n l α → Matrix n m α → Matrix o l α → Matrix o m α → Matrix (Sum n o) (Sum l m) α :=
  fun A B C D i j => by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact A i j
      | inr j => exact B i j
    | inr i =>
      cases j with
      | inl j => exact C i j
      | inr j => exact D i j

end Computable

end Matrix
