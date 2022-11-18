import Mathlib.Algebra.Ring.Basic

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
  inv x := 1 / x

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

def elementWise (f : α → α) : ArithVal α → ArithVal α
  | scalar x => scalar (f x)
  | vector n v => vector n (fun i => f (v i))
  | matrix n m A => matrix n m (fun i j => f (A i j))

def liftIntervalMap (f : Interval? α → Interval? β) (I : Interval? (ArithVal α)) 
  : Interval? (ArithVal β) := 
  match I with 
  | some ⟨scalar x, scalar y⟩ => 
      if let some I' := f <| some ⟨x, y⟩ then 
        some ⟨scalar I'.a, scalar I'.b⟩
      else none
  | _ => none
-- THIS IS HARD...

instance [Neg α] : Neg (ArithVal α) := ⟨elementWise Neg.neg⟩

instance [Inv α] : Inv (ArithVal α) := ⟨elementWise Inv.inv⟩

end ArithVal

/- Reals. -/

class RealLike (α : Type u) extends CommRing α, LE α, Inv α, Srt α, Exp α, Log α where 
  ofRat : Rat → α 
  ofRat_mono : ∀ {p q : Rat}, p ≤ q → ofRat p ≤ ofRat q
  ofRat_inj : ∀ {p q : Rat}, ofRat p = ofRat q → p = q
  ofRat_neg : ∀ {p : Rat}, ofRat (Rat.neg p) = -(ofRat p)

/- Bounded function. -/

class Bounded (α : Type) [RealLike α] (f : α → α) where
  bound : Nat → Interval? Rat → Interval? Rat 
  bound_correct : ∀ (prec : Nat) (x : α) (I : Interval? Rat), 
    x ∈ (I.map RealLike.ofRat : Interval? α) → 
    f x ∈ ((bound prec I).map RealLike.ofRat : Interval? α)

def arithBound (α : Type) [RealLike α] (f : α → α) (prec : Nat) [Bounded α f] 
  : Interval? (ArithVal Rat) → Interval? (ArithVal Rat) 
  | some I => none --TODO 
  | none   => none

instance (α : Type) [RealLike α] : Bounded α Neg.neg where 
  bound prec I := -I 
  bound_correct prec x I := by 
    cases I with 
    | none => simp [Interval?.map, Membership.mem]
    | some I => 
        simp only [Interval?.map, Membership.mem, Option.map, Interval.map, Neg.neg]
        intros a
        simp [RealLike.ofRat_neg]
        sorry

/- Arithmetic expressions where numerical values can be scalars, vectors, or 
matrices. -/

inductive ArithExpr : Type → Type (u + 1)
  | num : Rat → ArithExpr Rat
  | vec (n) : (Fin n → ArithExpr Rat) → ArithExpr (Fin n → Rat)
  | mat (n m) : (Fin n → Fin m → ArithExpr Rat) → ArithExpr (Fin n → Fin m → Rat)
  | val {α} : α → ArithExpr α 
  | var {α} : Nat → ArithExpr α
  | neg {α} [Neg α] : ArithExpr α → ArithExpr α
  | inv {α} [Inv α] : ArithExpr α → ArithExpr α
  | srt {α} [Srt α] : ArithExpr α → ArithExpr α
  | exp {α} [Exp α] : ArithExpr α → ArithExpr α
  | log {α} [Log α] : ArithExpr α → ArithExpr α
  | pow {β α} [HPow β Nat α] : ArithExpr β → Nat → ArithExpr α 
  | add {β₁ β₂ α} [HAdd β₁ β₂ α] : ArithExpr β₁ → ArithExpr β₂ → ArithExpr α 
  | mul {β₁ β₂ α} [HMul β₁ β₂ α] : ArithExpr β₁ → ArithExpr β₂ → ArithExpr α 

namespace ArithExpr

def sub {β₁ β₂ α} [HAdd β₁ β₂ α] [Neg β₂] 
  (e₁ : ArithExpr β₁) (e₂ : ArithExpr β₂) : ArithExpr α := 
  add e₁ (neg e₂)

def div {β₁ β₂ α} [HMul β₁ β₂ α] [Inv β₂] 
  (e₁ : ArithExpr β₁) (e₂ : ArithExpr β₂) : ArithExpr α := 
  mul e₁ (inv e₂)

open ArithVal

def approx (R) [RealLike R] {α} {n : Nat} (prec : Nat)
  : ArithExpr α → (∀ i : Fin n, Interval? (ArithVal Rat)) → Interval? (ArithVal Rat)
  | num x, _ => some ⟨scalar x, scalar x⟩
  | var i, I => if h : i < n then I ⟨i, h⟩ else none 
  | neg e, I => none --TODO: Bounded.bound Neg.neg prec (approx prec e I)
  | inv e, I => (approx e I)⁻¹
  | srt e, I => some ⟨sorry, sorry⟩
  | exp e, I => none
  | log e, I => none
  | _, _ => none

end ArithExpr
