import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Fin

namespace Vec

/-!
Named functions on vectors. Each of them corresponds to an atom.
-/

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] {α : Type w}

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Abs`. -/
def abs [Abs α] (x : m → α) : m → α :=
  fun i => Abs.abs (x i)

instance [Abs α] : Abs (m → α) := ⟨abs⟩

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.VecConst`. -/
def const (n : ℕ) (k : α) : Fin n → α  :=
  fun _ => k

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.VecToMatrix`. -/
def toMatrix {n : ℕ} (x : Fin n → α) : Matrix (Fin n) (Fin 1) α :=
  fun i => ![x i]

def map {β} (f : α → β) (v : m → α) : m → β :=
  fun i => f (v i)

section AddCommMonoid

variable [AddCommMonoid α] {m : Nat} {n : Nat} (x : Fin m → α) (y : Fin n → α)

open BigOperators

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Sum`. -/
def sum {m : Type} [Fintype m] (x : m → α) : α :=
  ∑ i, x i

open FinsetInterval

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.CumSum`. -/
def cumsum (t : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if h : 0 < n then ∑ j in [[⟨0, h⟩, i]], t j else 0

end AddCommMonoid


noncomputable section Real

/-!
Named functions on real vectors, including those defined in
`CvxLean.Lib.Math.Data.Real`. Each of them corresponds to an atom.
-/

open Real BigOperators

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Norm2`. -/
instance : Norm (m → ℝ) where
  norm x := sqrt (∑ i, (x i) ^ 2)

variable (x y : m → ℝ)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Exp`. -/
def exp : m → ℝ := fun i => Real.exp (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Log`. -/
def log : m → ℝ := fun i => Real.log (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Entr`. -/
def entr : m → ℝ := fun i => Real.entr (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.Huber`. -/
def huber : m → ℝ := fun i => Real.huber (x i)

/-- See `CvxLean.Tactic.DCP.AtomLibrary.Fns.KLDiv`. -/
def klDiv : m → ℝ := fun i => Real.klDiv (x i) (y i)

end Real

namespace Computable

/-!
Computable operations on matrices used in `RealToFloat`.
-/

variable {n : ℕ}

def toArray (x : Fin n → Float) : Array Float :=
  (Array.range n).map (fun i => if h : i < n then x ⟨i, h⟩ else 0)

def sum (x : Fin n → Float) : Float :=
  (toArray x).foldl Float.add 0

def cumsum (x : Fin n → Float) : Fin n → Float :=
  fun i => (((toArray x).toList.take (i.val + 1)).foldl Float.add 0)

end Computable

end Vec
