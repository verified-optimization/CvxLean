import CvxLean.Lib.Missing.Real

namespace Vec
variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] {α : Type w} (x y : m → α)

instance [Abs α] : Abs (m → α) := ⟨fun (x : m → α) (i : m) => Abs.abs (x i)⟩

def map (f : α → β) (x : m → α) : m → β := 
  fun i => f (x i)

end Vec

namespace Vec

section Basic
variable {m : Nat} {n : Nat} (x : Fin m → α) (y : Fin n → α)

/-- Produces a vector containing the first `k` entries of a given vector. -/
def take (k : ℕ) : (Fin (Min.min m k)) → α := 
  fun i => x ⟨i.1, lt_of_lt_of_le i.2 (min_le_left  _ _)⟩

end Basic

noncomputable def supNorm [Fintype n] [SemilatticeSup α] [OrderBot α] [Abs α] 
  (x : n → α) := 
  Finset.sup Finset.univ fun i => Abs.abs (x i)

section AddCommMonoid

variable {α} [AddCommMonoid α] {m : Nat} {n : Nat} (x : Fin m → α) (y : Fin n → α) 

open BigOperators

def sum {m : Type} [Fintype m] (x : m → α) : α :=
  ∑ i, x i

/-- Cumulative sum: The `i`th entry of the `cumsum` vector contains the sum of
  the first `i + 1` elements of the given vector. -/
noncomputable def cumsum : Fin m → α := 
  fun i => ∑ k, (take x (i.val + 1)) k

end AddCommMonoid

section Semiring

variable [Semiring α] {m : Nat} {n : Nat} (x : Fin m → α) (y : Fin n → α)

open BigOperators

/-- The convolution of `x` and `y` is the vector `z` that `z k = ∑ { x i * y j | i + j = k }`-/
def convolution : Fin (m + n - 1) → α := 
  fun k => ∑ i : Fin m, ∑ j : Fin n, if i.val + j.val = k.val then ((x i) * y j) else 0
 
def sum_squares : α := ∑ i, (x i) * x i

end Semiring

section Real

variable {m : Type u} {n : Type v} (x y : m → Real)

@[reducible]
noncomputable def exp : m → Real := 
  fun i => Real.exp (x i)

@[reducible]
noncomputable def log : m → Real := 
  fun i => Real.log (x i)

noncomputable def entr : m → Real := 
  fun i => Real.entr (x i)

noncomputable def huber [Fintype m] (x : m → Real) : m → Real := 
  fun i => Real.huber (x i)

noncomputable def kl_div : m → Real := 
  fun i => Real.kl_div (x i) (y i)

end Real

end Vec
