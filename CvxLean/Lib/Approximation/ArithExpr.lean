import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum

open Lean

/- Typeclasses for square root, exponential and logarithm. -/

class Srt (α : Type u) where
  srt : α → α

class Exp (α : Type u) where
  exp : α → α

class Log (α : Type u) where
  log : α → α

/- Rounding rationals and lemmas. -/

namespace Rat 

instance : HPow Rat Nat Rat where 
  hPow x n := mkRat (x.num ^ n) (x.den ^ n)

instance : Inv Rat where 
  inv := Rat.inv

def roundUp (prec : Nat) (x : Rat) : Rat := 
  let d := Nat.shiftLeft 2 prec
  mkRat (x * d).ceil d

def roundDown (prec : Nat) (x : Rat) : Rat := 
  let d := Nat.shiftLeft 2 prec
  mkRat (x * d).floor d

def divUp (prec : Nat) (x y : Rat) : Rat := 
  roundUp prec (x / y)

def divDown (prec : Nat) (x y : Rat) : Rat := 
  roundDown prec (x / y)

lemma roundUp_ub (prec : Nat) (x : Rat) : x ≤ roundUp prec x := by 
  sorry

lemma roundDown_lb (prec : Nat) (x : Rat) : roundDown prec x ≤ x := by 
  sorry

lemma neg_zero : (-0 : Rat) = 0 := rfl

lemma lt_of_neg_lt_neg {x y : Rat} : -x < -y → y < x := by 
  sorry  

lemma div_pos_of_pos_pos {x y : Rat} (hx : 0 < x) (hy : 0 < y) : 0 < x / y := by 
  sorry

end Rat

/- Intervals. -/

structure Interval (α : Type u) where 
  a : α
  b : α

def Interval? (α : Type u) : Type u := Option (Interval α)

def Interval.map {α} {β} (f : α → β) (x : Interval α) : Interval β := 
  ⟨f x.a, f x.b⟩

def Interval?.map {α} {β} (f : α → β) (x : Interval? α) : Interval? β := 
  Option.map (Interval.map f) x

instance {α} [LE α] : Membership α (Interval? α) where 
  mem x 
    | some I => I.a ≤ x ∧ x ≤ I.b
    | none   => False

instance {α} [Neg α] : Neg (Interval α) where 
  neg I := ⟨-I.b, -I.a⟩

instance {α} [Neg α] : Neg (Interval? α) := ⟨Option.map Neg.neg⟩

lemma mem_neg {α} [Neg α] [LE α] (x : α) (I : Interval? α) : x ∈ -I ↔ -x ∈ I := 
  sorry

instance {α} [Inv α] : Inv (Interval α) where 
  inv I := ⟨I.b⁻¹, I.a⁻¹⟩

instance {α} [Inv α] : Inv (Interval? α) := ⟨Option.map Inv.inv⟩

lemma mem_inv {α} [Inv α] [LE α] (x : α) (I : Interval? α) 
  : x ∈ I⁻¹ ↔ x⁻¹ ∈ I := 
  sorry

instance {α} [Srt α] : Srt (Interval α) where 
  srt I := ⟨Srt.srt I.a, Srt.srt I.b⟩

instance {α} [Srt α] : Srt (Interval? α) := ⟨Option.map Srt.srt⟩

lemma mem_srt {α} [Srt α] [LE α] (x : α) (I : Interval? α) 
  : x ∈ Srt.srt I ↔ Srt.srt x ∈ I := 
  sorry

instance {α} [Exp α] : Exp (Interval α) where 
  exp I := ⟨Exp.exp I.a, Exp.exp I.b⟩

instance {α} [Exp α] : Exp (Interval? α) := ⟨Option.map Exp.exp⟩

lemma mem_exp {α} [Exp α] [LE α] (x : α) (I : Interval? α) 
  : x ∈ Exp.exp I ↔ Exp.exp x ∈ I := 
  sorry

instance {α} [Log α] : Log (Interval α) where 
  log I := ⟨Log.log I.a, Log.log I.b⟩

instance {α} [Log α] : Log (Interval? α) := ⟨Option.map Log.log⟩

lemma mem_log {α} [Log α] [LE α] (x : α) (I : Interval? α) 
  : x ∈ Log.log I ↔ Log.log x ∈ I := 
  sorry

/- Values. -/

inductive ArithVal (α : Type u) : Type u
  | scalar : α → ArithVal α
  | vector (n) : (Fin n → α) → ArithVal α
  | matrix (n m) : (Fin n → Fin m → α) → ArithVal α

namespace ArithVal

@[reducible]
def carrier (α) : ArithVal α → Type u
  | scalar _ => α
  | vector n _ => Fin n → α
  | matrix n m _ => Fin n → Fin m → α

def elementWise (f : α → α) : ArithVal α → ArithVal α
  | scalar x => scalar (f x)
  | vector n v => vector n (fun i => f (v i))
  | matrix n m A => matrix n m (fun i j => f (A i j))

instance [Neg α] : Neg (ArithVal α) := ⟨elementWise Neg.neg⟩

instance [Inv α] : Inv (ArithVal α) := ⟨elementWise Inv.inv⟩

instance [Srt α] : Srt (ArithVal α) := ⟨elementWise Srt.srt⟩

end ArithVal

/- Reals. -/

class RealLike (R : Type u) extends 
  CommRing R, Preorder R, Inv R, Div R, Srt R, Exp R, Log R where 
  ofRat : Rat → R 
  ofRat_le_ofRat_iff : ∀ {p q : Rat}, p ≤ q ↔ ofRat p ≤ ofRat q
  ofRat_lt_ofRat_iff : ∀ {p q : Rat}, p < q ↔ ofRat p < ofRat q
  ofRat_inj : ∀ {p q : Rat}, ofRat p = ofRat q → p = q
  ofRat_zero : ofRat 0 = 0
  ofRat_one : ofRat 1 = 1
  ofRat_ofNat : ∀ {n : Nat} [Nat.AtLeastTwo n], ofRat (OfNat.ofNat n) = OfNat.ofNat n
  ofRat_neg : ∀ {p : Rat}, ofRat (Rat.neg p) = -(ofRat p)
  ofRat_inv : ∀ {p : Rat}, ofRat (Rat.inv p) = (ofRat p)⁻¹
  ofRat_add : ∀ {p q : Rat}, ofRat (p + q) = ofRat p + ofRat q
  ofRat_sub : ∀ {p q : Rat}, ofRat (p - q) = ofRat p - ofRat q
  ofRat_mul : ∀ {p q : Rat}, ofRat (p * q) = ofRat p * ofRat q
  ofRat_div : ∀ {p q : Rat}, ofRat (p / q) = ofRat p / ofRat q
  -- lemmas
  zero_lt_one : (0 : R) < 1
  srt_zero : Srt.srt (0 : R) = 0
  srt_nonneg : ∀ (x : R), 0 ≤ Srt.srt x
  srt_le : ∀ {x : R}, Srt.srt x ≤ x
  srt_lt_pos : ∀ {x : R}, 0 < x → Srt.srt x < x
  neg_le_neg : ∀ {x y : R}, x ≤ y → -y ≤ -x
  inv_le_inv : ∀ {x y : R}, x ≤ y → y⁻¹ ≤ x⁻¹

/- Bounded function. -/

class Bounded (R : Type u) [RealLike R] (f : R → R) where
  bound : Nat → Interval? Rat → Interval? Rat 
  bound_correct : ∀ (prec : Nat) (x : R) (I : Interval? Rat), 
    x ∈ (I.map RealLike.ofRat : Interval? R) → 
    f x ∈ ((bound prec I).map RealLike.ofRat : Interval? R)

def arithBound (R : Type u) [RealLike R] (f : R → R) (prec : Nat) [Bounded R f] 
  : ArithVal (Interval? Rat) → ArithVal (Interval? Rat) :=
  ArithVal.elementWise (Bounded.bound f prec)

instance (R : Type u) [RealLike R] : Bounded R Neg.neg where 
  bound _ I := -I 
  bound_correct prec x I := by 
    cases I with 
    | none => simp [Interval?.map, Membership.mem]
    | some I => 
        simp only [Interval?.map, Membership.mem, Option.map, Interval.map, Neg.neg]
        intros a
        simp [RealLike.ofRat_neg]
        exact ⟨RealLike.neg_le_neg a.2, RealLike.neg_le_neg a.1⟩

instance (R : Type u) [RealLike R] : Bounded R Inv.inv where 
  bound _ I := I⁻¹ 
  bound_correct prec x I := by 
    cases I with 
    | none => simp [Interval?.map, Membership.mem]
    | some I => 
        simp only [Interval?.map, Membership.mem, Option.map, Interval.map, Inv.inv]
        intros a
        simp [RealLike.ofRat_inv]
        exact ⟨RealLike.inv_le_inv a.2, RealLike.inv_le_inv a.1⟩

namespace Srt

def ratIter : Nat → Nat → Rat → Rat 
  | Nat.zero,   _,    x => if x = 0 then 1 else x
  | Nat.succ n, prec, x => 
      let y := ratIter n prec x
      Rat.roundUp prec ((y + x / y) / 2)

mutual 
  def ratUp (prec : Nat) (x : Rat) : Rat := 
    if 0 < x then ratIter prec prec x else 
    if x < 0 then -ratDown prec (-x) else 0

  def ratDown (prec : Nat) (x : Rat) : Rat := 
    if 0 < x then Rat.divDown prec x (ratIter prec prec x) else 
    if x < 0 then -ratUp prec (-x) else 0 
end
termination_by' measure (fun x => 
  match x with 
  | PSum.inl x => if x < 0 then 1 else 0
  | PSum.inr x => if x < 0 then 1 else 0) 
decreasing_by 
  have hneg : ¬(-x < 0) := by
    { intros hc; rw [←Rat.neg_zero] at hc; 
      exact (by assumption : ¬(0 < x)) (Rat.lt_of_neg_lt_neg hc) }
  show (if -x < 0 then 1 else 0) < (if x < 0 then 1 else 0) <;> 
  rw [if_pos (by assumption : x < 0), if_neg hneg] <;> 
  norm_num 

open RealLike

variable {R} [RealLike R]

lemma srt_ub_of_pos_pos (x b : R) 
  (hsrt : srt x < b) (hb : 0 < b) (hx : 0 < x) :
  srt x < (b + x / b) / 2 :=
  sorry 

lemma ratIter_bound (x : Rat) (prec n : Nat) (hx : (0 : R) < ofRat x) :
  srt (ofRat x) < (ofRat (ratIter n prec x) : R) := by 
  induction n with 
  | zero => 
      by_cases x = 0
      . simp [ratIter, h, ofRat_zero, srt_zero, ofRat_one, zero_lt_one]
      . simp [ratIter, h, srt_lt_pos hx]
  | succ n ih => 
      have unrounded : 
        (srt (ofRat x) : R) < 
        ofRat (((ratIter n prec x) + x / (ratIter n prec x)) / 2) := by 
        simp [ofRat_div, ofRat_add, ofRat_ofNat]
        refine srt_ub_of_pos_pos (ofRat x) (ofRat (ratIter n prec x)) ih ?_ hx 
        exact lt_of_le_of_lt (srt_nonneg (ofRat x)) ih
      exact lt_of_lt_of_le unrounded (ofRat_le_ofRat_iff.1 (Rat.roundUp_ub prec _))

lemma ratIter_pos (x : Rat) (prec n : Nat) (hx : (0 : R) < ofRat x) :
  (0 : R) < ofRat (ratIter n prec x) := 
  lt_of_le_of_lt (srt_nonneg (ofRat x)) (ratIter_bound x prec n hx)

-- lemma lb_sqrt_lower_bound:
--   assumes "0 ≤ real_of_float x"
--   shows "0 ≤ real_of_float (lb_sqrt prec x)"

lemma ratDown_lb (x : Rat) (prec n : Nat) (hx : (0 : R) < ofRat x) : 
  (0 : R) < ofRat (ratDown prec x) := by
  by_cases 0 < x 
  . simp [ratDown, h]
    sorry 
  . exfalso ; apply h ; rw [←ofRat_zero] at hx ; exact (ofRat_lt_ofRat_iff.2 hx)
    
    

end Srt

/- Arithmetic expressions where numerical values can be scalars, vectors, or 
matrices. -/

@[class]
inductive ArithType (R : Type u) : Type u → Type u
  | Scalar : ArithType R R
  | Vector (n : Nat) : ArithType R (Fin n → R)
  | Matrix (m n : Nat) : ArithType R (Fin m → Fin n → R)

inductive ArithExpr (B : Type u) : ∀ (γ : Type u) [ArithType B γ], Type (u + 1)
  | val {α} [ArithType B α] : α → ArithExpr B α
  | var {α} [ArithType B α] : Nat → ArithExpr B α
  | neg {α} [ArithType B α] [Neg α] : ArithExpr B α → ArithExpr B α
  | inv {α} [ArithType B α] [Inv α] : ArithExpr B α → ArithExpr B α
  | srt {α} [ArithType B α] [Srt α] : ArithExpr B α → ArithExpr B α
  | exp {α} [ArithType B α] [Exp α] : ArithExpr B α → ArithExpr B α
  | log {α} [ArithType B α] [Log α] : ArithExpr B α → ArithExpr B α
  | pow {β α} [ArithType B β] [ArithType B α] [HPow β Nat α] : ArithExpr B β → Nat → ArithExpr B α 
  | add {β₁ β₂ α} [ArithType B β₁] [ArithType B β₂] [ArithType B α] [HAdd β₁ β₂ α] : ArithExpr B β₁ → ArithExpr B β₂ → ArithExpr B α 
  | mul {β₁ β₂ α} [ArithType B β₁] [ArithType B β₂] [ArithType B α] [HMul β₁ β₂ α] : ArithExpr B β₁ → ArithExpr B β₂ → ArithExpr B α 

namespace ArithExpr

def sub {B β₁ β₂ α} [HAdd β₁ β₂ α] [ArithType B β₁] [ArithType B β₂] [ArithType B α] [Neg β₂] 
  (e₁ : ArithExpr B β₁) (e₂ : ArithExpr B β₂) : ArithExpr B α := 
  add e₁ (neg e₂)

def div {B β₁ β₂ α} [HMul β₁ β₂ α] [ArithType B β₁] [ArithType B β₂] [ArithType B α] [Inv β₂] 
  (e₁ : ArithExpr B β₁) (e₂ : ArithExpr B β₂) : ArithExpr B α := 
  mul e₁ (inv e₂)

open ArithVal

def interpret (R) [RealLike R] {n : Nat} {R'}
  : ∀ (h : ArithType R R'), ArithExpr R R' → (∀ i : Fin n, ArithVal R) → ArithVal R
  | ArithType.Scalar, val x, _ => scalar x
  | ArithType.Vector m, val x, _ => vector m x
  | ArithType.Matrix m n, val x, _ => matrix m n x
  | T, var i, Is => if h : i < n then Is ⟨i, h⟩ else scalar 0
  | T, neg e, Is => Neg.neg (interpret R T e Is)
  | T, inv e, Is => Inv.inv (interpret R T e Is)
  | T, srt e, Is => Srt.srt (interpret R T e Is)
  | T, exp e, Is => Exp.exp (interpret R T e Is)
  | T, log e, Is => Log.log (interpret R T e Is)
  | ArithType.Scalar, add e₁ e₂, Is => 
      match interpret R _ e₁ Is, interpret R _ e₂ Is with 
        | scalar x, scalar y => scalar (x + y)
        | scalar x, vector n y => vector n (fun i => x + y i)
        | vector n x, scalar y => vector n (fun i => x i + y)
        | vector n x, vector m y => 
            if h : n = m then vector n (fun i => x i + y (h ▸ i)) else scalar 0
        | _, _ => scalar 0
  | _, _, _ => sorry

def approx (R) [RealLike R] {n : Nat} (prec : Nat) {R'}
  : ∀ (h : ArithType Rat R'), ArithExpr Rat R' → (∀ i : Fin n, ArithVal (Interval? Rat)) → ArithVal (Interval? Rat)
  | ArithType.Scalar, val x, _ => scalar <| some ⟨x, x⟩
  | ArithType.Vector m, val x, _ => vector m <| fun i => some ⟨x i, x i⟩
  | ArithType.Matrix m n, val x, _ => matrix m n <| fun i j => some ⟨x i j, x i j⟩
  | T, var i, Is => if h : i < n then Is ⟨i, h⟩ else scalar none 
  | T, neg e, Is => arithBound R Neg.neg prec (approx R prec T e Is)
  | T, inv e, Is => arithBound R Inv.inv prec (approx R prec T e Is)
  | T, srt e, Is => sorry
  | T, exp e, Is => sorry
  | T, log e, Is => sorry
  | _, _, _ => sorry

end ArithExpr
