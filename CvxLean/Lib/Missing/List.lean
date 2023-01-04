import Mathbin.Data.Fin.Basic
import Mathlib.Algebra.Ring.Basic

def List.findIdx' (p : α → Prop) [DecidablePred p] : List α → Option Nat
| []     => none
| (a::l) => if p a then some 0 else (findIdx' p l).map Nat.succ

def List.toVec (x : List α) : Fin (x.length) → α := 
fun i => List.get x ⟨i, i.2⟩

def List.finRange' (d n : Nat) : List (Fin n) :=
  if hn : @LT.lt Nat instLTNat 0 n then (List.range d).map (Fin.ofNat' · hn) else []

def List.sum' [Zero α] [Add α] (L : List α) : α :=
  L.foldl (· + ·) 0
