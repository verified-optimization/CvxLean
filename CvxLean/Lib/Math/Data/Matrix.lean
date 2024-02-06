import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Array.Defs
import CvxLean.Lib.Math.Data.List
import CvxLean.Lib.Math.Data.Vec

/-!
Extra operations on matrices. Importantly, computable versions of matrix operations are defined
here, which are used by the real-to-float procedure.
-/

namespace Matrix

variable {m n} {α}

def const (k : α) : Matrix m n α :=
  fun _ _ => k

instance [Preorder α] : Preorder (Matrix m n α) where
  le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_refl _
  le_trans := fun _ _ _ hAB hBC i j => le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _

def abs (A : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => |A i j|

theorem vecCons_zero_zero {n} [Zero α] : vecCons (0 : α) (0 : Fin n → α) = 0 := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

theorem smul_vecCons {n} [Zero α] [SMulZeroClass ℝ α] (x : ℝ) (y : α) (v : Fin n → α) :
    x • vecCons y v = vecCons (x • y) (x • v) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

theorem add_vecCons {n} [Zero α] [SMulZeroClass ℝ α] [Add α] (x : α) (v : Fin n → α) (y : α)
    (w : Fin n → α) : vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [vecCons]

open BigOperators

def sum [Fintype m] [AddCommMonoid α] (X : Matrix m m α) : α :=
  ∑ i, (∑ j, X i j)


namespace Computable

/-!
Computable operations on matrices used in `RealToFloat`.
-/

variable {n m l : ℕ}

def toArray (A : Matrix (Fin n) (Fin n) Float) : Array (Array Float) :=
  (Array.range n).map <| fun i =>
    if h : i < n then Vec.Computable.toArray (A ⟨i, h⟩) else Array.mk <| List.replicate n 0

def dotProduct (v w : Fin n → Float) : Float :=
  (Array.zipWith (Vec.Computable.toArray v) (Vec.Computable.toArray w) Float.mul).foldl Float.add 0

infixl:72 " ⬝ᵥᶜ " => Matrix.Computable.dotProduct

def mulVec (M : Matrix (Fin n) (Fin m) Float) (v : (Fin m) → Float) : Fin n → Float :=
  fun i => (fun j => M i j) ⬝ᵥᶜ v

def vecMul (x : Fin n → Float) (M : Matrix (Fin n) (Fin m) Float) : Fin m → Float :=
  fun j => x ⬝ᵥᶜ fun i => M i j

def transpose {m n} {α} (M : Matrix m n α) : Matrix n m α :=
  fun i j => M j i

def diag {n} {α} (M : Matrix n n α) : n → α :=
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

private def minorAux (A : Matrix (Fin n.succ) (Fin n.succ) Float) (a b : Fin n.succ) :
    Matrix (Fin n) (Fin n) Float :=
  fun i j =>
    let i' : Fin n.succ := if i.val < a.val then i else i.succ;
    let j' : Fin n.succ := if j.val < b.val then j else j.succ;
    A i' j'

def minor (A : Matrix (Fin n) (Fin n) Float) (a b : Fin n) :
    Matrix (Fin n.pred) (Fin n.pred) Float :=
  match n with
  | 0 => fun _ => Fin.elim0
  | _ + 1 => minorAux A a b

def det {n : ℕ} (A : Matrix (Fin n) (Fin n) Float) : Float :=
  if h : 0 < n then
    if n == 1 then A ⟨0, h⟩ ⟨0, h⟩ else
      (List.finRange n).foldl (fun s i =>
        s + (-1) ^ (Float.ofNat i.val) * A i ⟨0, h⟩ * det (minor A i ⟨0, h⟩)) 0
  else 0

def cofactor (A : Matrix (Fin n) (Fin n) Float) : Matrix (Fin n) (Fin n) Float :=
  fun i j => (-1) ^ (Float.ofNat (i.val + j.val)) * (A i j)

def adjugate (A : Matrix (Fin n) (Fin n) Float) : Matrix (Fin n) (Fin n) Float :=
  transpose (cofactor A)

def inv (A : Matrix (Fin n) (Fin n) Float) : Matrix (Fin n) (Fin n) Float :=
  (1 / det A) • adjugate A

end Computable

end Matrix
