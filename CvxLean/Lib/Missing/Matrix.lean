import Mathlib.Data.Real.Basic
import Mathlib.Data.Array.Defs
import Mathbin.Data.Real.Basic
import Mathbin.LinearAlgebra.Matrix.Default
import Mathbin.LinearAlgebra.Matrix.PosDef
import CvxLean.Lib.Missing.List

namespace Matrix

attribute [-instance] Real.hasLt Real.hasLe Real.hasOne Real.hasZero Real.hasMul 
  Real.linearOrderedField Real.hasNatCast Real.hasAdd Real.addCommGroup 
  Real.hasNeg Real.hasSub Real.ring Real.addMonoid Real.monoid 
  Real.monoidWithZero Real.addCommMonoid Real.linearOrder 
  Real.conditionallyCompleteLinearOrder Real.orderedSemiring Real.hasSup

instance [Preorder α] : Preorder (Matrix m n α) :=
{ le := fun A B => ∀ i j, A i j ≤ B i j
  le_refl := fun _ _ _ => le_refl _
  le_trans := fun _ _ _ hAB hBC i j => le_trans (hAB i j) (hBC i j)
  lt_iff_le_not_le := fun _ _ => refl _ }

def sum [Fintype m] [AddCommMonoid α] (X : Matrix m m α) : α := 
  Finset.sum Finset.univ fun i => (Finset.sum Finset.univ fun j => X i j)

theorem vecCons_zero_zero {n} 
  : Matrix.vecCons (0 : ℝ) (0 : Fin n → ℝ) = 0 := by
  ext i ; refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]

theorem smul_vecCons {n} (x : ℝ) (y : ℝ) (v : Fin n → ℝ) 
  : x • Matrix.vecCons y v = Matrix.vecCons (x • y) (x • v) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]

theorem add_vecCons {n} (x : ℝ) (v : Fin n → ℝ) (y : ℝ) (w : Fin n → ℝ) 
  : Matrix.vecCons x v + Matrix.vecCons y w = Matrix.vecCons (x + y) (v + w) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]

theorem dotProduct_zero'' {m} [Fintype m] (x : m → ℝ) 
  : Matrix.dotProduct x 0 = 0 := by
  simp [Matrix.dotProduct]

theorem zero_dotProduct' {m} [Fintype m] (x : m → ℝ) 
  : Matrix.dotProduct 0 x = 0 := by
  simp [Matrix.dotProduct]

theorem dotProduct_smul' {m} [Fintype m] (x : m → ℝ) (y : m → ℝ) (a : ℝ) 
  : Matrix.dotProduct x (a • y) = a • Matrix.dotProduct x y := by
  unfold Matrix.dotProduct ; rw [Finset.smul_sum]
  apply congr_arg ; ext i ; simp ; ring

theorem smul_dotProduct' {m} [Fintype m] (x : m → ℝ) (y : m → ℝ) (a : ℝ) 
  : Matrix.dotProduct (a • x) y = a • Matrix.dotProduct x y := by
  unfold Matrix.dotProduct ; rw [Finset.smul_sum]
  apply congr_arg ; ext i ; simp ; ring

theorem dotProduct_add' {m} [Fintype m] (x : m → ℝ) (y y' : m → ℝ) 
  : Matrix.dotProduct x (y + y') = Matrix.dotProduct x y + Matrix.dotProduct x y' := by
  unfold Matrix.dotProduct ; simp only [←Finset.sum_add_distrib]
  apply congr_arg ; ext i ; simp ; ring

theorem add_dotProduct' {m} [Fintype m] (x x' : m → ℝ) (y : m → ℝ) 
  : Matrix.dotProduct (x + x') y = Matrix.dotProduct x y + Matrix.dotProduct x' y := by
  unfold Matrix.dotProduct ; simp only [←Finset.sum_add_distrib]
  apply congr_arg ; ext i ; simp ; ring

theorem zero_apply {n} (i : Fin n) (j : Fin n) 
  : (0 : Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
  rw [Pi.zero_apply, Pi.zero_apply]

attribute [instance] LinearOrder.decidable_le

def toUpperTri 
  {α m} [LE m] [DecidableRel (· ≤ · : m → m → Prop)] [Zero α] (A : Matrix m m α) 
  : Matrix m m α := 
  fun i j => if i ≤ j then A i j else 0

theorem toUpperTri_zero 
  {α m} [LE m] [DecidableRel (· ≤ · : m → m → Prop)] [Zero α] 
  : Matrix.toUpperTri (0 : Matrix m m α) = 0 := by
  funext i j ; simp [Matrix.toUpperTri] ; intros _ ; rfl

theorem toUpperTri_smul 
  {m} [Fintype m] [LE m] [DecidableRel (· ≤ · : m → m → Prop)] 
  (A : Matrix m m ℝ) (κ : ℝ)
  : κ • Matrix.toUpperTri A = Matrix.toUpperTri (κ • A) := by
  funext i j ; rw [Pi.smul_apply, Pi.smul_apply] ; simp only [Matrix.toUpperTri]
  by_cases h : i ≤ j <;> simp [h] ; rw [Pi.smul_apply, Pi.smul_apply] ; rfl

theorem toUpperTri_add 
  {m} [Fintype m] [LE m] [DecidableRel (· ≤ · : m → m → Prop)] 
  (A B : Matrix m m ℝ)
  : Matrix.toUpperTri (A + B) = Matrix.toUpperTri A + Matrix.toUpperTri B := by
  funext i j ; rw [Pi.add_apply, Pi.add_apply] ; simp only [Matrix.toUpperTri]
  by_cases h : i ≤ j <;> simp [h] ; rw [Pi.add_apply, Pi.add_apply]

theorem sum_zero {n} 
  : Matrix.sum (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  simp [Matrix.sum, Matrix.zero_apply]

theorem smul_sum {n} (X : Matrix (Fin n) (Fin n) ℝ) (κ : ℝ)
  : κ • Matrix.sum X = Matrix.sum (κ • X) := by
  unfold Matrix.sum ; rw [Finset.smul_sum]
  congr ; ext i ; rw [Finset.smul_sum] ; rfl 

theorem sum_add {n} (X Y : Matrix (Fin n) (Fin n) ℝ)
  : Matrix.sum X + Matrix.sum Y = Matrix.sum (X + Y) := by
  unfold Matrix.sum ; rw [←Finset.sum_add_distrib]
  congr ; ext i ; rw [←Finset.sum_add_distrib] ; rfl

theorem diag_smul' {m} [Fintype m] (x : ℝ) (A : Matrix m m ℝ) 
  : Matrix.diag (x • A) = x • Matrix.diag A := by
  rfl

theorem diagonal_zero' {n} 
  : Matrix.diagonal (0 : Fin n → ℝ) = 0 := by
  funext i j ; by_cases i = j <;> 
  simp [Matrix.diagonal, h] <;> rw [Pi.zero_apply, Pi.zero_apply] ; rfl

theorem diagonal_smul' {n} (d : Fin n → ℝ) (κ : ℝ)
  : κ • Matrix.diagonal d = Matrix.diagonal (κ • d) := by
  funext i j ; by_cases i = j <;>
  simp [Matrix.diagonal, h] <;> rw [Pi.smul_apply, Pi.smul_apply] <;>
  simp [h] ; exact MulZeroClass.mul_zero _

theorem diagonal_add' {n} (d₁ d₂ : Fin n → ℝ)
  : Matrix.diagonal d₁ + Matrix.diagonal d₂ = Matrix.diagonal (d₁ + d₂) := by
  funext i j ; by_cases i = j <;>
  simp [Matrix.diagonal, h] <;> rw [Pi.add_apply, Pi.add_apply] <;>
  simp [h] ; exact AddZeroClass.zero_add _

theorem trace_zero' {m} [Fintype m]
  : Matrix.trace (0 : Matrix m m ℝ) = 0 := by
  unfold Matrix.trace ; rw [Matrix.diag_zero]
  exact Finset.sum_const_zero

theorem trace_smul' {m} [Fintype m] (A : Matrix m m ℝ) (κ : ℝ)
  : Matrix.trace (κ • A) = κ • Matrix.trace A := by
  unfold Matrix.trace ; rw [Matrix.diag_smul', Finset.smul_sum] ; rfl

theorem trace_add' {m} [Fintype m] (A B : Matrix m m ℝ)
  : Matrix.trace (A + B) = Matrix.trace A + Matrix.trace B := by
  unfold Matrix.trace ; rw [Matrix.diag_add, ←Finset.sum_add_distrib] ; rfl

theorem transpose_zero' {m} [Fintype m] 
  : Matrix.transpose (0 : Matrix m m ℝ) = 0 := by
  funext i j ; simp [Matrix.transpose, id] ; rfl

theorem transpose_add' {m} [Fintype m] (A B : Matrix m m ℝ)
  : Matrix.transpose (A + B) = Matrix.transpose A + Matrix.transpose B := by
  funext i j ; simp [Matrix.transpose, id] ; rfl

theorem fromBlocks_zero {n m l o α} [Zero α] 
  : Matrix.fromBlocks (0 : Matrix n l α) (0 : Matrix n m α) (0 : Matrix o l α) (0 : Matrix o m α) = 0 := by
  funext i j ; cases i <;> cases j <;> simp [Matrix.fromBlocks] <;> rfl

theorem fromBlocks_smul' {n m l o} (κ : ℝ)
  (A : Matrix n l ℝ) (B : Matrix n m ℝ) (C : Matrix o l ℝ) (D : Matrix o m ℝ) 
  : κ • Matrix.fromBlocks A B C D = Matrix.fromBlocks (κ • A) (κ • B) (κ • C) (κ • D) := by
  funext i j ; cases i <;> cases j <;> rw [Pi.smul_apply, Pi.smul_apply] <;> 
  simp [Matrix.fromBlocks] <;> rfl

theorem mul_zero' {m} [Fintype m] (A : Matrix m m ℝ)
  : Matrix.mul A (0 : Matrix m m ℝ) = 0 := by
  funext ; exact Matrix.dotProduct_zero'' _

theorem zero_mul' {m} [Fintype m] (A : Matrix m m ℝ)
  : Matrix.mul (0 : Matrix m m ℝ) A = 0 := by
  funext ; exact Matrix.zero_dotProduct' _

theorem mul_smul' {m} [Fintype m] (κ : ℝ) (A : Matrix m m ℝ) (B : Matrix m m ℝ)
  : Matrix.mul A (κ • B) = κ • Matrix.mul A B := by
  funext ; exact Matrix.dotProduct_smul' _ _ _

theorem smul_mul' {m} [Fintype m] (κ : ℝ) (A : Matrix m m ℝ) (B : Matrix m m ℝ)
  : Matrix.mul (κ • A) B = κ • Matrix.mul A B := by
  funext ; exact Matrix.smul_dotProduct' _ _ _

theorem mul_add' {m} [Fintype m] (A : Matrix m m ℝ) (B C : Matrix m m ℝ)
  : Matrix.mul A (B + C) = Matrix.mul A B + Matrix.mul A C := by
  funext ; exact Matrix.dotProduct_add' _ _ _

theorem add_mul' {m} [Fintype m] (A B : Matrix m m ℝ) (C : Matrix m m ℝ)
  : Matrix.mul (A + B) C = Matrix.mul A C + Matrix.mul B C := by
  funext ; exact Matrix.add_dotProduct' _ _ _

theorem mulVec_zero' {m n} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
  : Matrix.mulVec A (0 : n → ℝ) = 0 := by
  funext i ; unfold Matrix.mulVec
  convert @Matrix.dotProduct_zero'' n _ (fun j => A i j) 
  sorry

theorem mulVec_smul' {m n} [Fintype m] [Fintype n] 
  (κ : ℝ) (A : Matrix m n ℝ) (v : n → ℝ)
  : Matrix.mulVec A (κ • v) = κ • Matrix.mulVec A v := by
  funext i ; unfold Matrix.mulVec 
  sorry

theorem mulVec_add' {m n} [Fintype m] [Fintype n] 
  (A : Matrix m n ℝ) (v w : n → ℝ)
  : Matrix.mulVec A (v + w) = Matrix.mulVec A v + Matrix.mulVec A w := by
  funext i ; unfold Matrix.mulVec
  sorry

-- Transform to arrays to compute. Avoiding mathbin matrix operations.
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

-- TODO: temporary hack because mathbin breaks infixl
-- infixl:72 " ⬝ᵥᶜ " => Matrix.Computable.dotProduct
macro:72 l:term:72 " ⬝ᵥᶜ " r:term:73 : term => 
  `(Matrix.Computable.dotProduct $l $r)

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

instance [Abs α] : Abs (Matrix m n α) where
  abs A i j := abs (A i j)

def mul [Mul α] [Add α] (M : Matrix (Fin l) (Fin m) α) (N : Matrix (Fin m) (Fin n) α) : Matrix (Fin l) (Fin n) α :=
fun i k => (fun j => M i j) ⬝ᵥᶜ (fun j => N j k)

-- TODO: temporary hack because mathbin breaks infixl
-- infixl:75 " ⬝ᶜ " => Matrix.Computable.mul
macro:75 l:term " ⬝ᶜ " r:term : term => 
  `(Matrix.Computable.mul $l $r)

def tr [Add α] (A : Matrix (Fin n) (Fin n) α) : α := 
  (Computable.vecToArray (fun i => A i i)).foldl (· + ·) 0

-- Project-specific.

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
