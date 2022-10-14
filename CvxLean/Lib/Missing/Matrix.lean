import Mathbin.LinearAlgebra.Matrix.Default
import Mathbin.LinearAlgebra.QuadraticForm.Basic

import Mathlib.Data.Array.Defs

import CvxLean.Lib.Missing.List
import CvxLean.Lib.Missing.Mathlib

attribute [-instance] coeDecidableEq

namespace Matrix

variable {α} [Zero α]

-- Transform to arrays to compute. Avoiding mathbin matrix operations.
namespace Computable

@[to_additive Pi.hasVadd]
instance Pi.hasSmul'  {I : Type} {f : I → Type v₁} [∀ i, HasSmul α <| f i] : HasSmul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

instance [HasSmul R α] : HasSmul R (Matrix m n α) :=
  Pi.hasSmul'

@[to_additive "See also `add_monoid.to_add_action`"]
instance (priority := 910) Mul.toHasSmul' (α : Type _) [Mul α] : HasSmul α α :=
  ⟨(· * ·)⟩

def vecToArray (v : Fin n → α) : Array α := 
  (Array.range n).map (fun i => if h : @LT.lt ℕ instLTNat i n then v ⟨i, h⟩ else 0)

def toArray (M : Matrix (Fin n) (Fin n) α) : Array (Array α) := 
  (vecToArray M).map vecToArray

def dotProduct [Mul α] [Add α] (v w : Fin n → α) : α :=
  ((Array.zip (vecToArray v) (vecToArray w)).map (fun ⟨a, b⟩ => a * b)).foldl (· + ·) 0

-- TODO: temporary hack because mathbin breaks infixl
-- infixl:72 " ⬝ᵥᶜ " => Matrix.Computable.dotProduct
macro:72 l:term:72 " ⬝ᵥᶜ " r:term:73 : term => 
  do return Lean.TSyntax.raw (← `(Matrix.Computable.dotProduct $l $r))

def mulVec [Mul α] [Add α] (M : Matrix (Fin m) (Fin n) α) (v : (Fin n) → α) : Fin m → α
  | i => (fun j => M i j) ⬝ᵥᶜ v

def vecMul [Mul α] [Add α] (v : (Fin m) → α) (M : Matrix (Fin m) (Fin n) α) : Fin n → α
  | j => v ⬝ᵥᶜ fun i => M i j

def transpose (α) (M : Matrix m n α) : Matrix n m α
  | x, y => M y x

def diag (α) (M : Matrix n n α) : n → α
  | x => M x x

instance [Add α] : Add (Matrix m n α) where
  add A B i j := (A i j) + (B i j)

instance [Sub α] : Sub (Matrix m n α) where
  sub A B i j := (A i j) - (B i j)

instance [HasAbs α] : HasAbs (Matrix m n α) where
  abs A i j := abs (A i j)

def mul [Mul α] [Add α] (M : Matrix (Fin l) (Fin m) α) (N : Matrix (Fin m) (Fin n) α) : Matrix (Fin l) (Fin n) α :=
fun i k => (fun j => M i j) ⬝ᵥᶜ (fun j => N j k)

-- TODO: temporary hack because mathbin breaks infixl
-- infixl:75 " ⬝ᶜ " => Matrix.Computable.mul
macro:75 l:term " ⬝ᶜ " r:term : term => 
  do return Lean.TSyntax.raw (← `(Matrix.Computable.mul $l $r))

def tr [Add α] (A : Matrix (Fin n) (Fin n) α) : α := 
  (Computable.vecToArray (fun i => A i i)).foldl (· + ·) 0

-- Project-specific.

def PosDef [Add α] [Mul α] [LT α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ x : (Fin n) → α, Matrix.Computable.vecMul x A ⬝ᵥᶜ x > 0

def PosSemidef [Add α] [Mul α] [LE α] (A : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ x : (Fin n) → α, Matrix.Computable.vecMul x A ⬝ᵥᶜ x ≥ 0

-- def affineConstraint [LE α] [Add α] [Mul α] (A X : Matrix (Fin n) (Fin n) α) (b : α) : Prop := 
-- Matrix.Computable.tr (Matrix.Computable.mul A X) = b

def posDefObjective [Add α] [Mul α] (C X : Matrix (Fin n) (Fin n) α) : α :=
Matrix.Computable.tr (Matrix.Computable.mul C X)

def quadForm [Add α] [Mul α] (A : Matrix (Fin n) (Fin n) α) (x : (Fin n) → α) :=
Matrix.Computable.vecMul x A ⬝ᵥᶜ x

def covarianceMatrix [Add α] [Mul α] [Div α] {N n : ℕ} [OfNat α N] (Y : Matrix (Fin N) (Fin n) α) (i j : Fin n) :=
((Computable.vecToArray Y).map (fun y => (y i) * y j)).foldl (· + ·) 0 / (OfNat.ofNat N)

def diagonal {n : Type u_3} {α : Type v} [DecidableEq n] [Zero α] (x : n → α) : Matrix n n α :=
fun i j => (if i = j then x i else 0)

def fromBlocks {l : Type}
  {m : Type}
    {n : Type}
      {o : Type}
        {α : Type} : Matrix n l α → Matrix n m α → Matrix o l α → Matrix o m α → Matrix (Sum n o) (Sum l m) α :=
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

-- Printing matrices.
section Print

def print [ToString α] {n : Nat} (M : Matrix (Fin n) (Fin n) α) 
  : IO String := do 
  let mut ret := "["
  for i in (List.finRange' n n) do 
    ret := ret ++ (if i.val = 0 then "[" else ",[")
    for j in (List.finRange' n n) do
      ret := ret ++ ToString.toString (M i j) 
      ret := ret ++ (if j.val = n - 1 then "" else ",")
    
    ret := ret ++ "]\n"
  
  return ret

end Print

open Matrix

instance [Fintype m] [LE α] : LE (Matrix m m α) := Pi.hasLe

noncomputable def sum [Fintype m] [AddCommMonoidₓ α] (X : Matrix m m α) : α := 
  ∑ i, (∑ j, X i j)

def abs [HasAbs α] (X : Matrix m n α) : Matrix m n α := 
  fun i j => HasAbs.abs (X i j)

noncomputable def posDefObjective [Fintype m] [OrderedSemiring α] (C X : Matrix m m α) : α :=
trace (C ⬝ X)

def affineConstraint [Fintype m] [OrderedSemiring α] (A X : Matrix m m α) (b : α) : Prop := 
trace (A ⬝ X) = b

instance [Preorderₓ α] : Preorderₓ (Matrix m n α) :=
{ Le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_reflₓ _
  le_trans := fun _ _ _ hAB hBC i j => le_transₓ (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _ }

end Matrix
