import Std.Classes.SetNotation
import Std.Data.Rat

open Std

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
  toString b := s!"[{b.center} ± {b.radius}]"

notation "[" center " ± " radius "]" => Ball.mk center radius

def Ball.map {α β} (f : α → β) (b : Ball α) : Ball β :=
  ⟨f b.center, f b.radius⟩

@[extern "ball_sqrt"]
opaque Ball.sqrt : @&Nat → (Ball Rat) → Ball Rat

@[extern "ball_exp"]
opaque Ball.exp : @&Nat → (Ball Rat) → Ball Rat

@[extern "ball_linear_system"]
opaque Ball.linearSystem : @&Nat → @&Nat → @&Nat → Array (Array (Ball Rat)) → Array (Array (Ball Rat)) → Array (Array (Ball Rat)) → Array (Array (Ball Rat))