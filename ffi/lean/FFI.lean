import Lean
import Std.Classes.SetNotation

open Lean

structure Ball (α) where 
  center : α
  radius : α

instance (α) [LE α] [Add α] [Sub α] : Membership α (Ball α) where
  mem x b := x ≥ (b.center - b.radius) ∧ x ≤ (b.center + b.radius)

instance (α) [LE α] [Add α] [Sub α] : HasSubset (Ball α) where 
  Subset b₁ b₂ := ∀ x ∈ b₁, x ∈ b₂

instance (α) [Inhabited α] : Inhabited (Ball α) where
  default := ⟨default, default⟩

instance (α) [ToString α] : ToString (Ball α) where
  toString b := s!"[{b.center} +/- {b.radius}]"

def Ball.map {α β} (f : α → β) (b : Ball α) : Ball β :=
  ⟨f b.center, f b.radius⟩

structure Vector (n : Nat) (α) where
  a : Array α 
  h : a.size = n := by decide

def Vector.toFun {n} {α} : Vector n α → Fin n → α
  | ⟨x, hx⟩ => fun ⟨i, hi⟩ => x.get ⟨i, hx.symm ▸ hi⟩

def Matrix (r c : Nat) (α) := 
  Vector r (Vector c α)

def Matrix.mk (r c : Nat) 
  (A : Array (Array α)) 
  (h₁ : A.size = r := by decide)
  (h₂ : ∀ i : Fin r, (A.get (h₁ ▸ i)).size = c) : Matrix r c α :=
  sorry

def Matrix.toFun {r c} {α} (x : Matrix r c α) : Fin r → Fin c → α :=
  fun i => ((Vector.toFun x) i).toFun

def v : Vector 2 Nat := Vector.mk #[1, 2]

#check Matrix.mk

@[extern "ball_sqrt"]
opaque Ball.sqrt : @&Nat → (Ball Rat) → Ball Rat



