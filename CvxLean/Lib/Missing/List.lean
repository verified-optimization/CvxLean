import Mathbin.Data.Fin.Basic
import Mathlib.Algebra.Ring.Basic
import CvxLean.Lib.Missing.Nat

def List.findIdx' (p : α → Prop) [DecidablePred p] : List α → Option Nat
| []     => none
| (a::l) => if p a then some 0 else (findIdx' p l).map Nat.succ

def List.toVec (x : List α) : Finₓ (x.length) → α := 
fun i => List.get x ⟨i, by rw [←Nat.hasLt_eq_instLTNat]; exact i.2⟩

def List.finRange' (d n : Nat) : List (Fin n) :=
  if hn : @LT.lt Nat instLTNat 0 n then (List.range d).map (Fin.ofNat' · hn) else []

def List.sum' [Zero α] [Add α] (L : List α) : α :=
  L.foldl (· + ·) 0
