import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs

open Lean

instance {α} : Inhabited (Array α) where
  default := Array.empty

def Array.zeros [Zero α] (n : Nat) : Array α :=
  Array.mk (List.replicate n 0)

def DArray.zeros [Zero α] (a b : Nat) : Array (Array α) :=
  Array.mk (List.replicate b (Array.zeros a))

def Array.filterIdx (as : Array α) (f : Nat → Bool) := Id.run do
  let mut bs := #[]
  for h : i in [:as.size] do
    if f i then
      bs := bs.push (as.get ⟨i, h.2⟩)
  return bs

@[specialize] def Array.zipWithMAux (f : α → β → MetaM γ)
    (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) :
    MetaM (Array γ) := do
  if h : i < as.size then
    let a := as.get ⟨i, h⟩;
    if h : i < bs.size then
      let b := bs.get ⟨i, h⟩;
      return ← zipWithMAux f as bs (i+1) <| cs.push <| ← f a b
    else
      pure cs
  else
    pure cs
termination_by _ => as.size - i

def Array.zipWithM (f : α → β → MetaM γ) (as : Array α) (bs : Array β) :
    MetaM (Array γ) :=
  zipWithMAux f as bs 0 #[]

def Array.drop (n : ℕ) (as : Array α) : Array α :=
  Array.mk (as.data.drop n)

def Array.take (n : ℕ) (as : Array α) : Array α :=
  Array.mk (as.data.take n)
