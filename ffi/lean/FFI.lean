import Lean

open Lean

structure Ball where 
  center : Rat
  radius : Rat

instance : Inhabited Ball where
  default := ⟨0, 0⟩

instance : ToString Ball where
  toString b := s!"[{b.center} +/- {b.radius}]"

@[extern "ball_sqrt"]
opaque Ball.sqrt : @&Nat → Ball → Ball


