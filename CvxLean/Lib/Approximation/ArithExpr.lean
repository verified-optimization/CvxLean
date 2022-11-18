import Mathlib.Algebra.Group.Defs

class Sqrt (α : Type u) where
  sqrt : α → α

class Exp (α : Type u) where
  exp : α → α

class Log (α : Type u) where
  log : α → α

-- The idea is that this works with vector and matrices too.

open Lean

inductive ArithVal : Type u
  | num : Rat → ArithVal
  | vec {n} : (Fin n → Rat) → ArithVal
  | matrix {n m} : (Fin n → Fin m → Rat) → ArithVal

inductive ArithExpr : Type u → Type (u + 1)
  | val : ArithVal.{u} → ArithExpr ArithVal.{u}
  | var {α} : Nat → ArithExpr α
  | neg {α} [Neg α] : ArithExpr α → ArithExpr α
  | inv {α} [Inv α] : ArithExpr α → ArithExpr α
  | sqrt {α} [Sqrt α] : ArithExpr α → ArithExpr α
  | exp {α} [Exp α] : ArithExpr α → ArithExpr α
  | log {α} [Log α] : ArithExpr α → ArithExpr α
  | pow {β α} [HPow β Nat α] : ArithExpr β → Nat → ArithExpr α 
  | add {β₁ β₂ α} [HAdd β₁ β₂ α] : ArithExpr β₁ → ArithExpr β₂ → ArithExpr α 
  | mul {β₁ β₂ α} [HMul β₁ β₂ α] : ArithExpr β₁ → ArithExpr β₂ → ArithExpr α 

namespace ArithExpr

end ArithExpr
