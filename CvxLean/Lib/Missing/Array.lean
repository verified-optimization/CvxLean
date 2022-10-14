import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Defs

def Array.zeroes [Zero α] (n : Nat) : Array α := 
  Array.mk (List.repeat' 0 n)

def DArray.zeroes [Zero α] (a b : Nat) : Array (Array α) :=
  Array.mk (List.repeat' (Array.zeroes a) b)

def Array.filterIdx (as : Array α) (f : Nat → Bool) := Id.run do
  let mut bs := #[]
  for i in [:as.size] do
    if h : i < as.size then -- TODO: Deduce this from for loop.
      if f i then
        bs := bs.push (as.get ⟨i, h⟩)
  return bs

@[specialize] def zipWithMAux (f : α → β → Lean.MetaM γ) (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) : Lean.MetaM (Array γ) := do
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

def Array.zipWithM (f : α → β → Lean.MetaM γ) (as : Array α) (bs : Array β)  : 
  Lean.MetaM (Array γ) := zipWithMAux f as bs 0 #[]

def Array.drop (n : ℕ) (as : Array α) : Array α :=
  Array.mk (as.data.drop n)

def Array.take (n : ℕ) (as : Array α) : Array α :=
  Array.mk (as.data.take n)
