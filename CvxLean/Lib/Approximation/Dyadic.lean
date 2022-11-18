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
  mk' (-x.m) x.e

instance : Neg Dyadic where 
  neg := neg 

lemma neg_m (x : Dyadic) : (-x).m = -(x.m) := rfl

lemma neg_e (x : Dyadic) : (-x).e = x.e := rfl

lemma neg_zero : (-0 : Dyadic) = 0 := rfl

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

lemma le_refl (x : Dyadic) : x ≤ x := Int.le_refl _

lemma neg_le_neg {x y : Dyadic} : x ≤ y → -y ≤ -x := by
  simp [LE.le, Dyadic.le, neg_e, neg_m, ←Int.neg_mul_eq_neg_mul]
  exact Int.neg_le_neg

lemma le_of_neg_le_neg {x y : Dyadic} : -x ≤ -y → y ≤ x := by 
  simp [LE.le, Dyadic.le, neg_e, neg_m, ←Int.neg_mul_eq_neg_mul]
  exact Int.le_of_neg_le_neg

def lt (x y : Dyadic) : Prop := 
  x ≤ y ∧ ¬(x ≥ y)

instance : LT Dyadic where 
  lt := lt

lemma neg_lt_neg {x y : Dyadic} : x < y → -y < -x := by
  simp [LT.lt, Dyadic.lt]
  exact fun hpos hneg => ⟨neg_le_neg hpos, fun hc => hneg (le_of_neg_le_neg hc)⟩

lemma lt_of_neg_lt_neg {x y : Dyadic} : -y < -x → x < y := by
  simp [LT.lt, Dyadic.lt]
  exact fun hpos hneg => ⟨le_of_neg_le_neg hpos, fun hc => hneg (neg_le_neg hc)⟩

instance : DecidableRel (LE.le : Dyadic → Dyadic → Prop) := 
  fun x y => Int.decLe _ _

instance : DecidableRel (LT.lt : Dyadic → Dyadic → Prop) := 
  fun a b => inferInstanceAs (Decidable (And _ (Not _)))

/-- Round Dyadic. -/

def roundUpPos (prec : Nat) (d : Dyadic) : Dyadic :=
  if d.e < 0 then
    mk ((d.m * (Int.pow 2 prec) + 1) / (Int.pow 2 d.e.natAbs)) (-prec)
  else 
    mk (d.m * (Int.pow 2 (d.e.natAbs + prec))) (-prec)

def roundDownPos (prec : Nat) (d : Dyadic) : Dyadic :=
  if d.e < 0 then
    mk ((d.m * (Int.pow 2 prec) - 1) / (Int.pow 2 d.e.natAbs)) (-prec)
  else 
    mk (d.m * (Int.pow 2 (d.e.natAbs + prec))) (-prec)

def roundUp (prec : Nat) (d : Dyadic) : Dyadic := 
  if d < 0 then - roundDownPos prec (-d) else roundUpPos prec d

#eval roundUp 10 (Dyadic.mk 3 (-13))

def roundDown (prec : Nat) (d : Dyadic) : Dyadic := 
  if d < 0 then - roundUpPos prec (-d) else roundDownPos prec d

theorem roundUp_upper_bound (prec : Nat) (d : Dyadic) : 
  d ≤ roundUp prec d := 
  sorry

def roundDown_lower_bound (prec : Nat) (d : Dyadic) : 
  roundDown prec d ≤ d := 
  sorry

/- Division. -/

-- NOTE: THESE ARE WRONG.

def divUp  (prec : Nat) (x y : Dyadic) : Dyadic := 
  roundUp prec <| mk (x.m / y.m) (x.e - y.e)

def divDown (prec : Nat) (x y : Dyadic) : Dyadic := 
  roundDown prec <| mk (x.m / y.m) (x.e - y.e)

/- Square root. -/

private def sqrtIteration : Nat → Nat → Dyadic → Dyadic 
  |    _,   0, x => Dyadic.mk 1 (((Nat.log2 x.m.natAbs) + x.e) / 2 + 1)
  | prec, n+1, x => 
      let y := sqrtIteration prec n x
      (Dyadic.mk 1 (-1)) * roundUp prec (y + (divUp prec x y))

-- Should I just use Rat instead of daydic for everything>???

#eval sqrtIteration 1 1 (2 : Dyadic)
#eval sqrtIteration 10 0 (2 : Dyadic)
#eval sqrtIteration 10 10 (2 : Dyadic)
#eval divUp 10 (2 : Dyadic) (sqrtIteration 10 0 (2 : Dyadic))
#eval let y := Dyadic.mk 3 (1)
   (divUp 10 2 y)
  -- (Dyadic.mk 1 (-1)) * roundUp 10 (y + (divUp 10 2 y))

mutual 
  def sqrtUp (prec : Nat) (x : Dyadic) : Dyadic := 
    if 0 < x then sqrtIteration prec prec x else 
    if x < 0 then -sqrtDown prec (-x) else 0

  def sqrtDown (prec : Nat) (x : Dyadic) : Dyadic := 
    if 0 < x then divDown prec x (sqrtIteration prec prec x) else 
    if x < 0 then -sqrtUp prec (-x) else 0 
end
termination_by' measure (fun x => 
  match x with 
  | PSum.inl x => if x < 0 then 1 else 0
  | PSum.inr x => if x < 0 then 1 else 0) 
decreasing_by 
  have hneg : ¬(-x < 0) := by
    { intros hc; rw [←neg_zero] at hc; 
      exact (by assumption : ¬(0 < x)) (lt_of_neg_lt_neg hc) }
  show (if -x < 0 then 1 else 0) < (if x < 0 then 1 else 0) <;> 
  rw [if_pos (by assumption : x < 0), if_neg hneg] <;> 
  norm_num 

end Dyadic

open Lean

instance : HPow Rat Nat Rat where 
  hPow x n := mkRat (x.num ^ n) (x.den ^ n)

def Rat.roundUp (prec : Nat) (x : Rat) : Rat := 
  mkRat (Rat.ceil (x * (OfNat.ofNat (2 ^ prec)))) (2 ^ prec)

def Rat.roundDown (prec : Nat) (x : Rat) : Rat := 
  mkRat (Rat.floor (x * (OfNat.ofNat (2 ^ prec)))) (2 ^ prec)

def Rat.divUp (prec : Nat) (x y : Rat) : Rat := 
  Rat.roundUp prec (x / y)

def Rat.divDown (prec : Nat) (x y : Rat) : Rat := 
  Rat.roundDown prec (x / y)

-- x / y
-- 

def sqrtRatIter : Nat → Nat → Rat → Rat 
  | Nat.zero,   _,    x => x / 2
  | Nat.succ n, prec, x => 
      let y := sqrtRatIter n prec x
      y - Rat.roundUp prec ((y - x / y) / 2)

mutual 
  def sqrtRatUp (prec : Nat) (x : Rat) : Rat := 
    if 0 < x then sqrtRatIter prec prec x else 
    if x < 0 then -sqrtRatDown prec (-x) else 0

  def sqrtRatDown (prec : Nat) (x : Rat) : Rat := 
    if 0 < x then Rat.divDown prec x (sqrtRatIter prec prec x) else 
    if x < 0 then -sqrtRatUp prec (-x) else 0 
end
termination_by' measure (fun x => 
  match x with 
  | PSum.inl x => if x < 0 then 1 else 0
  | PSum.inr x => if x < 0 then 1 else 0) 
decreasing_by sorry


#eval sqrtRatUp 10 (200000000 : Rat)
