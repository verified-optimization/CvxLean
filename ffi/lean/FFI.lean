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

@[extern "ball_sqrt"]
opaque Ball.sqrt : @&Nat → (Ball Rat) → Ball Rat
