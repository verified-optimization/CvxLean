import Mathlib.Algebra.Group.Defs

structure Interval (α) [LE α] where 
  a : α
  b : α
  -- h : a ≤ b

namespace Interval 

variable {α} [LE α]

def set (I : Interval α) : Set α := 
  { x | I.a ≤ x ∧ x ≤ I.b }

theorem set_ext (a b : α) : 
  ∀ x, x ∈ (Interval.mk a b).set ↔ a ≤ x ∧ x ≤ b := fun _ => Iff.refl _

end Interval 
