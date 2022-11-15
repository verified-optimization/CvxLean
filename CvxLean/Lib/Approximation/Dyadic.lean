import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.NormNum

/-- Representing ideal floats as m * 2 ^ e where m, e ∈ ℤ. -/

structure Dyadic where mk' :: 
  m : Int 
  e : Int 

namespace Dyadic 

def mkPos : Nat → Int → Dyadic
  | 0, _ => mk' 0 0
  | Nat.succ m, e =>
      if m.succ % 2 = 0 then 
        mkPos (m.succ / 2) (e + 1)
      else 
        mk' m.succ e
decreasing_by 
  apply Nat.div_lt_self (Nat.zero_lt_succ _) (by norm_num)

def mk (m e : Int) : Dyadic := 
  if m < 0 then 
    let d := mkPos (-m).natAbs e
    mk' (-d.m) d.e 
  else 
    mkPos m.natAbs e

theorem ext_iff {p q : Dyadic} : p = q ↔ p.m = q.m ∧ p.e = q.e := by
  cases p <;> cases q <;> simp

instance : DecidableEq Dyadic := fun a b => 
  decidable_of_decidable_of_iff (Iff.symm (@ext_iff a b))

instance : ToString Dyadic where 
  toString x := toString x.m ++ "*2^" ++ toString x.e

instance : OfNat Dyadic n where 
  ofNat := mk n 0

instance : Inhabited Dyadic where 
  default := 0

instance : Coe Int Dyadic where 
  coe x := mk x 0

def zero : Dyadic := 
  0

instance : Zero Dyadic where 
  zero := zero

def neg (x : Dyadic) : Dyadic := 
  mk (-x.m) x.e

instance : Neg Dyadic where 
  neg := neg 

def abs (x : Dyadic) : Dyadic := 
  mk (if x.m < 0 then -x.m else x.m) x.e

def add (x y : Dyadic) : Dyadic := 
  if x.e ≤ y.e then 
    mk (x.m + y.m * Int.pow 2 (y.e - x.e).toNat) x.e
  else 
    mk (y.m + x.m * Int.pow 2 (x.e - y.e).toNat) y.e

instance : Add Dyadic where
  add := add 

def sub (x y : Dyadic) : Dyadic := 
  x + (-y)

instance : Sub Dyadic where 
  sub := sub 

def mul (x y : Dyadic) : Dyadic := 
  mk (x.m * y.m) (x.e + y.e)

instance : Mul Dyadic where 
  mul := mul 

def le (x y : Dyadic) : Prop := 
    x.m * Int.pow 2 (x.e - y.e).toNat ≤ y.m * Int.pow 2 (y.e - x.e).toNat

instance : LE Dyadic where 
  le := le

def lt (x y : Dyadic) : Prop := 
  x ≤ y ∧ x ≠ y

instance : LT Dyadic where 
  lt := lt

instance : DecidableRel (LE.le : Dyadic → Dyadic → Prop) := 
  fun x y => Int.decLe _ _

instance : DecidableRel (LT.lt : Dyadic → Dyadic → Prop) := 
  fun a b => inferInstanceAs (Decidable (And _ (Not _)))

/-- Round Dyadic. -/

def roundUpPos (prec : Nat) (d : Dyadic) : Dyadic :=
  if d.e < 0 then
    mk ((d.m * (Int.pow 2 prec)) / (Int.pow 2 d.e.natAbs) + 1) (-prec)
  else 
    mk (d.m * (Int.pow 2 (d.e.natAbs + prec)) + 1) (-prec)

def roundDownPos (prec : Nat) (d : Dyadic) : Dyadic :=
  if d.e < 0 then
    mk ((d.m * (Int.pow 2 prec)) / (Int.pow 2 d.e.natAbs) - 1) (-prec)
  else 
    mk (d.m * (Int.pow 2 (d.e.natAbs + prec)) - 1) (-prec)

def roundUp (prec : Nat) (d : Dyadic) : Dyadic := 
  if d < 0 then - roundDownPos prec (-d) else roundUpPos prec d

def roundDown (prec : Nat) (d : Dyadic) : Dyadic := 
  if d < 0 then - roundUpPos prec (-d) else roundDownPos prec d

theorem roundUp_upper_bound (prec : Nat) (d : Dyadic) : 
  d ≤ roundUp prec d := 
  sorry

def roundDown_lower_bound (prec : Nat) (d : Dyadic) : 
  roundDown prec d ≤ d := 
  sorry

end Dyadic
