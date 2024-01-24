import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Array.Defs
import CvxLean.Lib.Math.Data.List


namespace Matrix

def const (k : α) : Matrix m n α :=
  fun _ _ => k

instance [Preorder α] : Preorder (Matrix m n α) where
  le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_refl _
  le_trans := fun _ _ _ hAB hBC i j => le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _

def abs (A : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => Abs.abs (A i j)

instance : Abs (Matrix m n ℝ) := ⟨abs⟩

theorem vecCons_zero_zero {n} [Zero R] : vecCons (0 : R) (0 : Fin n → R) = 0 := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

theorem smul_vecCons {n} [Zero R] [SMulZeroClass ℝ R] (x : ℝ) (y : R) (v : Fin n → R) :
    x • vecCons y v = vecCons (x • y) (x • v) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

theorem add_vecCons {n} [Zero R] [SMulZeroClass ℝ R] [Add R] (x : R) (v : Fin n → R) (y : R)
    (w : Fin n → R) : vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

open BigOperators

def sum [Fintype m] [AddCommMonoid α] (X : Matrix m m α) : α :=
  ∑ i, (∑ j, X i j)


namespace Computable

/-!
Computable operations on matrices used in `RealToFloat`.
-/

variable {α} [Zero α] [Mul α] [Add α]

def vecToArray (x : Fin n → α) : Array α :=
  (Array.range n).map (fun i => if h : i < n then x ⟨i, h⟩ else 0)

def toArray (A : Matrix (Fin n) (Fin n) α) : Array (Array α) :=
  (vecToArray A).map vecToArray

def dotProduct (v w : Fin n → α) : α :=
  (Array.zipWith (vecToArray v) (vecToArray w) (· * ·)).foldl (· + ·) 0

infixl:72 " ⬝ᵥᶜ " => Matrix.Computable.dotProduct

def mulVec (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : Fin m → α :=
  fun i => (fun j => M i j) ⬝ᵥᶜ v

def vecMul (x : (Fin m) → α) (M : Matrix (Fin m) (Fin n) α) : Fin n → α :=
  fun j => x ⬝ᵥᶜ fun i => M i j

def transpose (α) (M : Matrix m n α) : Matrix n m α :=
  fun i j => M j i

def diag (α) (M : Matrix n n α) : n → α :=
  fun i => M i i

def mul (M : Matrix (Fin l) (Fin m) α) (N : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin l) (Fin n) α :=
  fun i k => (fun j => M i j) ⬝ᵥᶜ (fun j => N j k)

infixl:75 " ⬝ᶜ " => Matrix.Computable.mul

def tr [Add α] (A : Matrix (Fin n) (Fin n) α) : α :=
  (vecToArray (fun i => A i i)).foldl (· + ·) 0

def PosDef [LT α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ x : (Fin n) → α, vecMul x A ⬝ᵥᶜ x > 0

def PosSemidef [LE α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ x : (Fin n) → α, vecMul x A ⬝ᵥᶜ x ≥ 0

def posDefObjective [Add α] [Mul α] (C X : Matrix (Fin n) (Fin n) α) : α :=
  tr (C ⬝ᶜ X)

def quadForm (A : Matrix (Fin n) (Fin n) α) (x : (Fin n) → α) :=
  vecMul x A ⬝ᵥᶜ x

def covarianceMatrix [Div α] {N n : ℕ} [OfNat α N]
    (Y : Matrix (Fin N) (Fin n) α) (i j : Fin n) : α :=
  ((vecToArray Y).map (fun y => (y i) * y j)).foldl (· + ·) 0 / (OfNat.ofNat N)

def diagonal {n : Type u} {α : Type v} [DecidableEq n] [Zero α] (x : n → α) :
    Matrix n n α :=
  fun i j => (if i = j then x i else 0)

def fromBlocks {l : Type} {m : Type} {n : Type} {o : Type} {α : Type} :
    Matrix n l α → Matrix n m α → Matrix o l α → Matrix o m α →
    Matrix (n ⊕ o) (l ⊕ m) α :=
  fun A B C D i j =>
    match i with
    | Sum.inl i =>
      match j with
      | Sum.inl j => A i j
      | Sum.inr j => B i j
    | Sum.inr i =>
      match j with
      | Sum.inl j => C i j
      | Sum.inr j => D i j

end Computable

end Matrix
