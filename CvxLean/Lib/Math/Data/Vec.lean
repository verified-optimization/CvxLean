import CvxLean.Lib.Math.Data.Real

namespace Vec

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] {α : Type w}

def abs [Abs α] (x : m → α) : m → α :=
  fun i => Abs.abs (x i)

instance [Abs α] : Abs (m → α) := ⟨abs⟩

section AddCommMonoid

variable [AddCommMonoid α] {m : Nat} {n : Nat} (x : Fin m → α) (y : Fin n → α)

open BigOperators

def sum {m : Type} [Fintype m] (x : m → α) : α :=
  ∑ i, x i

end AddCommMonoid

noncomputable section Real

open Real BigOperators

instance : Norm (m → ℝ) where
  norm x := sqrt (∑ i, (x i) ^ 2)

variable (x y : m → Real)

def exp : m → Real :=
  fun i => Real.exp (x i)

def log : m → Real :=
  fun i => Real.log (x i)

def entr : m → Real :=
  fun i => Real.entr (x i)

def huber : m → Real :=
  fun i => Real.huber (x i)

def klDiv : m → Real :=
  fun i => Real.klDiv (x i) (y i)

end Real

end Vec
