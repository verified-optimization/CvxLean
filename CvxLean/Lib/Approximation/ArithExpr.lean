import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast
import Std.Data.Nat.Gcd

open Lean

/- Typeclasses for square root, exponential and logarithm. -/

class Srt (α : Type u) where
  srt : α → α

class Exp (α : Type u) where
  exp : α → α

class Log (α : Type u) where
  log : α → α

/- Nat lemmas. -/

namespace Nat 

end Nat 

/- Rounding rationals and lemmas. -/

namespace Rat 

instance : HPow Rat Nat Rat where 
  hPow x n := mkRat (x.num ^ n) (x.den ^ n)

instance : Inv Rat where 
  inv := Rat.inv

section Lemmas 

lemma neg_zer : (-0 : Rat) = 0 := rfl

lemma neg_num {x : Rat} : (-x).num = -(x.num) := rfl

lemma neg_neg (x : Rat) : -(-x) = x := by 
  show Rat.neg (Rat.neg x) = x
  simp [Rat.neg]

lemma neg_neg_of_pos {x : Rat} : 0 < x → -x < 0 := by 
  show Rat.lt _ _ → Rat.lt _ _
  intros hpos
  by_cases (-x).num < 0 <;> simp [Rat.lt, h]
  rename ¬(-x).num < 0 => hnotlt
  by_cases (-x).num = 0 <;> simp [h]
  . exfalso
    simp [Rat.lt] at hpos 
    have hnegxnum : -(x.num) = 0 := h  
    have hc : x.num = 0 := Int.neg_zero ▸ Int.eq_neg_of_eq_neg hnegxnum.symm
    exact (Int.ne_of_lt hpos) hc.symm
  . exfalso 
    have hgt : (-x).num > 0 := match Int.lt_trichotomy (-x).num 0 with 
      | Or.inl hlt => absurd hlt hnotlt
      | Or.inr (Or.inl heq) => absurd heq h
      | Or.inr (Or.inr hgt) => hgt
    have hgtnum : -(x.num) > 0 := (by rfl : (-x).num = -(x.num)) ▸ hgt
    have hlt : x.num < 0 := 
      Int.neg_neg x.num ▸ (Int.neg_zero ▸ Int.neg_lt_neg hgtnum)
    simp [Rat.lt, hlt] at hpos
    exact (Int.not_le.mpr hpos) (Int.le_of_lt hlt)

#check Int

lemma lt_of_neg_lt_neg {x y : Rat} : -x < -y → y < x := by 
  show Rat.lt _ _ → Rat.lt _ _
  intros hnn
  by_cases y.num < 0 ∧ x.num ≥ 0 <;> simp [Rat.lt, h]
  rename ¬(y.num < 0 ∧ x.num ≥ 0) => hnand
  by_cases y.num = 0 <;> simp [h]
  . by_contra hc 
    simp [Rat.lt] at hnn
    have hnlt : ¬((-x).num < 0) := fun hlt => by 
      have hlt' : -x.num < 0 := (by rfl : (-x).num = -(x.num)) ▸ hlt
      exact hc <| Int.neg_neg x.num ▸ (Int.neg_zero ▸ Int.neg_lt_neg hlt')
    simp [hnlt] at hnn 
    rename y.num = 0 => hyeq
    by_cases (-x).num = 0 <;> simp [h] at hnn 
    . have hgtnum : -(y.num) > 0 := (by rfl : (-y).num = -(y.num)) ▸ hnn
      rw [hyeq, Int.neg_zero] at hgtnum
      exact Int.lt_irrefl 0 hgtnum 
    . rename ¬(-x).num = 0 => hxneq
      by_cases (-x).num > 0 ∧ (-y).num ≤ 0 <;> simp [h] at hnn 
      have hgt : (-x).num > 0 := match Int.lt_trichotomy (-x).num 0 with 
        | Or.inl hlt => absurd hlt hnlt 
        | Or.inr (Or.inl heq) => absurd heq hxneq 
        | Or.inr (Or.inr hgt) => hgt
      exact (Int.neg_zero ▸ hyeq ▸ neg_num ▸ not_and.mp h hgt) (Int.le_refl 0)
  . rename ¬(y.num = 0) => hyneq
    by_cases y.num > 0 ∧ x.num ≤ 0 <;> simp [h]
    . simp [Rat.lt] at hnn 
      have hnegynge : ¬((-y).num ≥ 0) := fun hlt => by 
        rw [neg_num] at hlt
        refine Int.lt_irrefl 0 (Int.lt_trans h.1 ?_)
        refine Int.lt_iff_le_and_ne.mpr ⟨?_, hyneq⟩
        exact Int.neg_neg y.num ▸ (Int.neg_zero ▸ Int.neg_le_neg hlt)
      simp [hnegynge] at hnn
      sorry 
    . sorry 

lemma pos_iff_num_pos {x : Rat} : 0 < x ↔ 0 < x.num := by 
  simp [LT.lt, Rat.lt, GT.gt]
  exact @decide_eq_true_iff _ (Int.decLt _ _)

lemma den_pos_of_nz_den {x : Rat} (hden : x.den ≠ 0) : (0 : Int) < x.den := by 
  revert hden
  induction x.den with 
  | zero => intros h ; contradiction
  | succ n ih => 
      simp [Nat.cast_succ]
      by_cases n = 0
      . rw [h] ; simp
      . exact Int.lt_add_one_of_le (Int.le_of_lt (ih h))

lemma inv_pos_of_pos_nz_den {x : Rat} (hx : 0 < x) (hden : x.den ≠ 0) 
  : 0 < x⁻¹ := by 
  simp [Inv.inv, Rat.inv]
  by_cases x.num < 0 <;> simp [h]
  . by_contra
    apply Int.lt_irrefl (0 : Int)
    exact Int.lt_trans (pos_iff_num_pos.mp hx) h
  . by_cases x.num = 0 <;> simp [h]
    . exact hx
    . simp [LT.lt, Rat.lt]
      exact den_pos_of_nz_den hden

-- TODO: move 
lemma Int.ofNat_div (n m : Nat) 
  : Int.ofNat (n / m) = Int.ofNat n / Int.ofNat m := rfl

-- TODO: move 
lemma Int.div_pos_of_le {x y : Int} (hy : 0 < y) (hle : y ≤ x) : 0 < x / y := by 
  let ⟨n, hn⟩ := Int.eq_succ_of_zero_lt (Int.lt_of_lt_of_le hy hle)
  let ⟨m, hm⟩ := Int.eq_succ_of_zero_lt hy
  rw [hn, hm, ←Int.ofNat_div]
  have hif := And.intro (Nat.zero_lt_succ m) (hm ▸ (hn ▸ hle))
  rw [Int.ofNat_le] at hif
  rw [Nat.div_eq, if_pos hif]
  apply Int.ofNat_succ_pos

lemma Nat.le_cast {x y : ℕ} (h : x ≤ y) 
  : (Nat.cast x : Int) ≤ Nat.cast y := by
  induction h with 
  | refl => exact Int.le_refl _ 
  | @step m _ ih => 
      simp [Nat.cast_succ]
      have hmaddone : (Nat.cast m : Int) ≤ Nat.cast m + 1 := 
        Int.le_add_of_nonneg_right (Int.le_of_lt Int.zero_lt_one)
      exact Int.le_trans ih hmaddone

lemma mul_pos_of_pos_pos {x y : Rat} (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by 
  simp [HMul.hMul, Mul.mul, Rat.mul]
  simp [LT.lt, Rat.lt]
  apply Int.mul_pos;
  { have hgcdpos : (0 : Int) < ↑(Nat.gcd (Int.natAbs x.num) y.den) := by
    { have hxnz := (Int.ne_of_lt (pos_iff_num_pos.1 hx)).symm
      have habs := Int.natAbs_pos_of_ne_zero hxnz
      have hgcd : 0 < Nat.gcd (Int.natAbs x.num) y.den := 
        Nat.gcd_pos_of_pos_left _ habs
      let ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_lt hgcd).symm;
      rw [hn] ; apply Int.ofNat_succ_pos }
    apply Int.div_pos_of_le hgcdpos;
    { rw [←Int.ofNat_natAbs_eq_of_nonneg x.num (Int.le_of_lt (pos_iff_num_pos.1 hx))] 
      rw [Int.ofNat_eq_cast]
      apply Nat.le_cast;
      have hxnumne := (Int.ne_of_lt (pos_iff_num_pos.1 hx)).symm
      have habspos := Int.natAbs_pos_of_ne_zero hxnumne;
      exact Nat.gcd_le_left y.den habspos; } }
  { sorry }

lemma div_pos_of_pos_pos {x y : Rat} 
  (hx : 0 < x) (hy : 0 < y) (hyden : y.den ≠ 0) : 0 < x / y := by 
  simp [HDiv.hDiv, Div.div, Rat.div]
  sorry

end Lemmas 

section Rounding

def roundUp (prec : Nat) (x : Rat) : Rat := 
  let d := Nat.shiftLeft 2 prec
  mkRat (x * d).ceil d

def roundDown (prec : Nat) (x : Rat) : Rat := 
  let d := Nat.shiftLeft 2 prec
  mkRat (x * d).floor d

lemma roundUp_ub (prec : Nat) (x : Rat) : x ≤ roundUp prec x := by 
  cases x
  simp [roundUp]
  sorry

lemma roundDown_lb (prec : Nat) (x : Rat) : roundDown prec x ≤ x := by 
  sorry

def divUp (prec : Nat) (x y : Rat) : Rat := 
  roundUp prec (x / y)

def divDown (prec : Nat) (x y : Rat) : Rat := 
  roundDown prec (x / y)

lemma divUp_ub (prec : Nat) (x y : Rat) : x / y ≤ divUp prec x y :=
  roundUp_ub prec (x / y)

lemma divDown_lb (prec : Nat) (x y : Rat) : divDown prec x y ≤ x / y :=
  roundDown_lb prec (x / y)

end Rounding

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

/- Generic arithmetic values. -/

inductive ArithVal (α : Type u) : Type u
  | scalar : α → ArithVal α
  | vector (n) : (Fin n → α) → ArithVal α
  | matrix (n m) : (Fin n → Fin m → α) → ArithVal α

namespace ArithVal

def elementWise (f : α → α) : ArithVal α → ArithVal α
  | scalar x => scalar (f x)
  | vector n v => vector n (fun i => f (v i))
  | matrix n m A => matrix n m (fun i j => f (A i j))

instance [Neg α] : Neg (ArithVal α) := ⟨elementWise Neg.neg⟩

instance [Inv α] : Inv (ArithVal α) := ⟨elementWise Inv.inv⟩

instance [Srt α] : Srt (ArithVal α) := ⟨elementWise Srt.srt⟩

instance [Exp α] : Exp (ArithVal α) := ⟨elementWise Exp.exp⟩

instance [Log α] : Log (ArithVal α) := ⟨elementWise Log.log⟩

end ArithVal

/- Reals. -/

class RealLike (R : Type u) extends 
  CommRing R, Preorder R, Inv R, Div R, Srt R, Exp R, Log R where 
  ofRat : Rat → R 
  ofRat_le_ofRat_iff : ∀ {p q : Rat}, p ≤ q ↔ ofRat p ≤ ofRat q
  ofRat_lt_ofRat_iff : ∀ {p q : Rat}, p < q ↔ ofRat p < ofRat q
  ofRat_zero : ofRat 0 = 0
  ofRat_one : ofRat 1 = 1
  ofRat_ofNat : ∀ {n : Nat} [Nat.AtLeastTwo n], ofRat (OfNat.ofNat n) = OfNat.ofNat n
  ofRat_neg : ∀ {p : Rat}, ofRat (Rat.neg p) = -(ofRat p)
  ofRat_inv : ∀ {p : Rat}, ofRat (Rat.inv p) = (ofRat p)⁻¹
  ofRat_add : ∀ {p q : Rat}, ofRat (p + q) = ofRat p + ofRat q
  ofRat_sub : ∀ {p q : Rat}, ofRat (p - q) = ofRat p - ofRat q
  ofRat_mul : ∀ {p q : Rat}, ofRat (p * q) = ofRat p * ofRat q
  ofRat_div : ∀ {p q : Rat}, ofRat (p / q) = ofRat p / ofRat q
  zero_lt_one : (0 : R) < 1
  srt_zero : Srt.srt (0 : R) = 0
  srt_nonneg : ∀ (x : R), 0 ≤ Srt.srt x
  srt_le : ∀ {x : R}, Srt.srt x ≤ x
  srt_lt_pos : ∀ {x : R}, 0 < x → Srt.srt x < x
  neg_le_neg : ∀ {x y : R}, x ≤ y → -y ≤ -x
  inv_le_inv : ∀ {x y : R}, x ≤ y → y⁻¹ ≤ x⁻¹

namespace RealLike

lemma pos_iff_pos_ofReal {R} [RealLike R] {x : Rat} 
  : 0 < x ↔ (0 : R) < ofRat x := by
  rw [←ofRat_zero]
  exact ofRat_lt_ofRat_iff

end RealLike

/- Bounded function. -/

class Bounded (R : Type u) [RealLike R] (f : R → R) where
  bound : Nat → Interval? Rat → Interval? Rat 
  bound_correct : ∀ (prec : Nat) (x : R) (I : Interval? Rat), 
    x ∈ (I.map RealLike.ofRat : Interval? R) → 
    f x ∈ ((bound prec I).map RealLike.ofRat : Interval? R)

def arithBound (R : Type u) [RealLike R] (f : R → R) (prec : Nat) [Bounded R f] 
  : ArithVal (Interval? Rat) → ArithVal (Interval? Rat) :=
  ArithVal.elementWise (Bounded.bound f prec)

namespace Neg

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

end Neg

namespace Inv

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

end Inv

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
    have hIter := ratIter_pos x prec prec hx
    rw [←pos_iff_pos_ofReal] at hx hIter
    sorry 
  . exfalso ; apply h ; rw [←ofRat_zero] at hx ; exact (ofRat_lt_ofRat_iff.2 hx)
    
end Srt

/- Arithmetic expressions where numerical values can be scalars, vectors, or 
matrices. -/

inductive ArithExpr (R : Type u) 
  | val : ArithVal R → ArithExpr R
  | var : Nat → ArithExpr R
  | neg : ArithExpr R → ArithExpr R
  | inv : ArithExpr R → ArithExpr R
  | srt : ArithExpr R → ArithExpr R
  | exp : ArithExpr R → ArithExpr R
  | log : ArithExpr R → ArithExpr R
  | pow : ArithExpr R → Nat → ArithExpr R 
  | add : ArithExpr R → ArithExpr R → ArithExpr R
  | mul : ArithExpr R → ArithExpr R → ArithExpr R 

namespace ArithExpr

def sub {R} (e₁ : ArithExpr R) (e₂ : ArithExpr R) : ArithExpr R := 
  add e₁ (neg e₂)

def div {R} (e₁ : ArithExpr R) (e₂ : ArithExpr R) : ArithExpr R := 
  mul e₁ (inv e₂)

open ArithVal

def interpret (R) [RealLike R] {n : Nat}
  : ArithExpr R → (∀ i : Fin n, ArithVal R) → ArithVal R
  | val x, _ => x
  | var i, Is => if h : i < n then Is ⟨i, h⟩ else scalar 0
  | neg e, Is => Neg.neg (interpret R e Is)
  | inv e, Is => Inv.inv (interpret R e Is)
  | srt e, Is => Srt.srt (interpret R e Is)
  | exp e, Is => Exp.exp (interpret R e Is)
  | log e, Is => Log.log (interpret R e Is)
  | add e₁ e₂, Is => 
      match (interpret R e₁ Is), (interpret R e₂ Is) with 
        | scalar x, scalar y => scalar (x + y)
        | scalar x, vector n y => vector n (fun i => x + y i)
        | vector n x, scalar y => vector n (fun i => x i + y)
        | vector n x, vector m y => 
            if h : n = m then 
              vector n (fun i => x i + y (h ▸ i)) 
            else scalar 0
        | _, _ => scalar 0
  | _, _ => sorry

def approx (R) [RealLike R] {n : Nat} (prec : Nat) 
  : ArithExpr Rat → (∀ i : Fin n, ArithVal (Interval? Rat)) → ArithVal (Interval? Rat)
  | val (scalar x), _ => scalar <| some ⟨x, x⟩
  | val (vector n x), _ => vector n <| fun i => some ⟨x i, x i⟩
  | val (matrix n m x), _ => matrix n m <| fun i j => some ⟨x i j, x i j⟩
  | var i, Is => if h : i < n then Is ⟨i, h⟩ else scalar none 
  | neg e, Is => arithBound R Neg.neg prec (approx R prec e Is)
  | inv e, Is => arithBound R Inv.inv prec (approx R prec e Is)
  | srt e, Is => sorry
  | exp e, Is => sorry
  | log e, Is => sorry
  | _, _ => sorry

end ArithExpr
