import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Array.Defs
import CvxLean.Lib.Math.Data.List
import CvxLean.Lib.Math.Data.Vec

namespace Matrix

def const (k : α) : Matrix m n α :=
  fun _ _ => k

instance [Preorder α] : Preorder (Matrix m n α) where
  le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_refl _
  le_trans := fun _ _ _ hAB hBC i j => le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _

def abs (A : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => |A i j|

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

def toArray (A : Matrix (Fin n) (Fin n) Float) : Array (Array Float) :=
  (Array.range n).map <| fun i =>
    if h : i < n then Vec.Computable.toArray (A ⟨i, h⟩) else Array.mk <| List.replicate n 0

def dotProduct (v w : Fin n → Float) : Float :=
  (Array.zipWith (Vec.Computable.toArray v) (Vec.Computable.toArray w) Float.mul).foldl Float.add 0

infixl:72 " ⬝ᵥᶜ " => Matrix.Computable.dotProduct

def mulVec (M : Matrix (Fin m) (Fin n) Float) (v : (Fin n) → Float) : Fin m → Float :=
  fun i => (fun j => M i j) ⬝ᵥᶜ v

def vecMul (x : Fin m → Float) (M : Matrix (Fin m) (Fin n) Float) : Fin n → Float :=
  fun j => x ⬝ᵥᶜ fun i => M i j

def transpose (M : Matrix m n α) : Matrix n m α :=
  fun i j => M j i

def diag (M : Matrix n n α) : n → α :=
  fun i => M i i

def mul (M : Matrix (Fin l) (Fin m) Float) (N : Matrix (Fin m) (Fin n) Float) :
    Matrix (Fin l) (Fin n) Float :=
  fun i k => (fun j => M i j) ⬝ᵥᶜ (fun j => N j k)

def sum (A : Matrix (Fin n) (Fin n) Float) : Float :=
  Vec.Computable.sum (fun i => Vec.Computable.sum (A i))

infixl:75 " ⬝ᶜ " => Matrix.Computable.mul

def trace (A : Matrix (Fin n) (Fin n) Float) : Float :=
  (Vec.Computable.toArray (fun i => A i i)).foldl (· + ·) 0

def covarianceMatrix {N n : ℕ} (Y : Matrix (Fin N) (Fin n) Float) (i j : Fin n) : Float :=
  Vec.Computable.sum (fun k => (Y k i) * (Y k j)) / (OfNat.ofNat N)
  --((vecToArray Y).map (fun y => (y i) * y j)).foldl (· + ·) 0 / (OfNat.ofNat N)

def diagonal (x : Fin n → Float) : Matrix (Fin n) (Fin n) Float :=
  fun i j => (if i = j then x i else 0)

def fromBlocks {l : Type} {m : Type} {n : Type} {o : Type} {α : Type} :
    Matrix n l α → Matrix n m α → Matrix o l α → Matrix o m α → Matrix (n ⊕ o) (l ⊕ m) α :=
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

def toUpperTri (A : Matrix (Fin n) (Fin n) Float) : Matrix (Fin n) (Fin n) Float :=
  fun i j => if i ≤ j then A i j else 0

end Computable

end Matrix
