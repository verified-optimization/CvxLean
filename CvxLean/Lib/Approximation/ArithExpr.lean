import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormCast
import Std.Data.Nat.Gcd

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

-- axiom den_nonzero : ∀ (x : Rat), x.den ≠ 0

-- instance : HPow Rat Nat Rat where 
--   hPow x n := mkRat (x.num ^ n) (x.den ^ n)

instance : Inv Rat where 
  inv := Rat.inv

-- section Lemmas 

-- lemma neg_zero : (-0 : Rat) = 0 := rfl

-- lemma neg_neg (x : Rat) : -(-x) = x := by 
--   show Rat.neg (Rat.neg x) = x
--   simp [Rat.neg]

-- lemma neg_neg_of_pos {x : Rat} : 0 < x → -x < 0 := 
--   sorry

-- lemma lt_of_neg_lt_neg {x y : Rat} : -x < -y → y < x := 
--   sorry

-- lemma pos_iff_num_pos {x : Rat} : 0 < x ↔ 0 < x.num := 
--   sorry

-- lemma den_pos_of_nz_den {x : Rat} (hden : x.den ≠ 0) : (0 : Int) < x.den := 
--   sorry

-- lemma inv_pos_of_pos_nz_den {x : Rat} (hx : 0 < x) (hden : x.den ≠ 0) 
--   : 0 < x⁻¹ := 
--   sorry

-- -- TODO: move 
-- lemma Int.ofNat_div (n m : Nat) 
--   : Int.ofNat (n / m) = Int.ofNat n / Int.ofNat m := rfl

-- -- TODO: move 
-- lemma Int.div_pos_of_le {x y : Int} (hy : 0 < y) (hle : y ≤ x) : 0 < x / y := 
--   sorry

-- lemma Nat.le_cast {x y : ℕ} (h : x ≤ y) 
--   : (Nat.cast x : Int) ≤ Nat.cast y :=
--   sorry

-- lemma mul_pos_of_pos_pos {x y : Rat} (hx : 0 < x) (hy : 0 < y) : 0 < x * y :=
--   sorry

-- lemma div_pos_of_pos_pos {x y : Rat} 
--   (hx : 0 < x) (hy : 0 < y) (hyden : y.den ≠ 0) : 0 < x / y := 
--   sorry

-- end Lemmas 

section Rounding

def roundUp (prec : Nat) (x : Rat) : Rat := 
  let d := Nat.shiftLeft 2 prec
  mkRat (x * d).ceil d

def roundDown (prec : Nat) (x : Rat) : Rat := 
  let d := Nat.shiftLeft 2 prec
  mkRat (x * d).floor d

lemma roundUp_ub (prec : Nat) (x : Rat) : x ≤ roundUp prec x := 
  sorry

lemma roundDown_lb (prec : Nat) (x : Rat) : roundDown prec x ≤ x := 
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

-- inductive ArithVal (α : Type u) : Type u
--   | scalar : α → ArithVal α
--   | vector (n) : (Fin n → α) → ArithVal α
--   | matrix (n m) : (Fin n → Fin m → α) → ArithVal α

-- namespace ArithVal

-- def elementWise (f : α → α) : ArithVal α → ArithVal α
--   | scalar x => scalar (f x)
--   | vector n v => vector n (fun i => f (v i))
--   | matrix n m A => matrix n m (fun i j => f (A i j))

-- instance [Neg α] : Neg (ArithVal α) := ⟨elementWise Neg.neg⟩

-- instance [Inv α] : Inv (ArithVal α) := ⟨elementWise Inv.inv⟩

-- instance [Srt α] : Srt (ArithVal α) := ⟨elementWise Srt.srt⟩

-- instance [Exp α] : Exp (ArithVal α) := ⟨elementWise Exp.exp⟩

-- instance [Log α] : Log (ArithVal α) := ⟨elementWise Log.log⟩

-- end ArithVal

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
  srt_bound : ∀ {x b : R}, 0 < b → 0 < x → srt x < b → srt x < (b + x / b) / 2
  neg_le_neg : ∀ {x y : R}, x ≤ y → -y ≤ -x
  inv_le_inv : ∀ {x y : R}, x ≤ y → y⁻¹ ≤ x⁻¹

namespace RealLike

-- lemma pos_iff_pos_ofReal {R} [RealLike R] {x : Rat} 
--   : 0 < x ↔ (0 : R) < ofRat x := by
--   rw [←ofRat_zero]
--   exact ofRat_lt_ofRat_iff

end RealLike

/- Bounded function. -/

class Bounded (R : Type u) [RealLike R] (f : R → R) where
  bound : Nat → Interval? Rat → Interval? Rat 
  bound_correct : ∀ (prec : Nat) (x : R) (I : Interval? Rat), 
    x ∈ (I.map RealLike.ofRat : Interval? R) → 
    f x ∈ ((bound prec I).map RealLike.ofRat : Interval? R)

-- def arithBound (R : Type u) [RealLike R] (f : R → R) (prec : Nat) [Bounded R f] 
--   : ArithVal (Interval? Rat) → ArithVal (Interval? Rat) :=
--   ArithVal.elementWise (Bounded.bound f prec)

def arithBound (R : Type u) [RealLike R] (f : R → R) (prec : Nat) [Bounded R f] 
  : Interval? Rat → Interval? Rat :=
  Bounded.bound f prec

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

def sqrtLowerBound : Rat → Rat := fun x => x / 2

def sqrtUpperBound : Rat → Rat := fun x => x / 2

instance (R : Type u) [RealLike R] : Bounded R Srt.srt where 
  bound _ 
    | some I => some <| ⟨sqrtLowerBound I.a, sqrtUpperBound I.b⟩
    | none => none
  bound_correct prec x I := sorry

end Srt

namespace Exp

def expLowerBound : Rat → Rat := fun x => 1

def expUpperBound : Rat → Rat := fun x => 1

instance (R : Type u) [RealLike R] : Bounded R Exp.exp where 
  bound _ 
    | some I => some <| ⟨expLowerBound I.a, expUpperBound I.b⟩
    | none => none
  bound_correct prec x I := sorry

end Exp

namespace Log

def logLowerBound : Rat → Rat := fun x => 0

def logUpperBound : Rat → Rat := fun x => 0

instance (R : Type u) [RealLike R] : Bounded R Log.log where 
  bound _ 
    | some I => some <| ⟨logLowerBound I.a, logUpperBound I.b⟩
    | none => none
  bound_correct prec x I := sorry

end Log

/- Arithmetic expressions where numerical values can be scalars, vectors, or 
matrices. -/

inductive ArithExpr (R : Type u) 
  | val : R → ArithExpr R --ArithVal R → ArithExpr R
  | var : Nat → ArithExpr R
  | neg : ArithExpr R → ArithExpr R
  | inv : ArithExpr R → ArithExpr R
  | srt : ArithExpr R → ArithExpr R
  | exp : ArithExpr R → ArithExpr R
  | log : ArithExpr R → ArithExpr R
  --| pow : ArithExpr R → Nat → ArithExpr R 
  | add : ArithExpr R → ArithExpr R → ArithExpr R
  | mul : ArithExpr R → ArithExpr R → ArithExpr R 

namespace ArithExpr

def sub {R} (e₁ : ArithExpr R) (e₂ : ArithExpr R) : ArithExpr R := 
  add e₁ (neg e₂)

def div {R} (e₁ : ArithExpr R) (e₂ : ArithExpr R) : ArithExpr R := 
  mul e₁ (inv e₂)

-- open ArithVal

def Option.map2 {α β γ : Type u} : (α → β → γ) → Option α → Option β → Option γ
  | f, some x, some y => some (f x y)
  | _, _, _ => none

def interpret (R) [RealLike R] {n : Nat}
  -- : ArithExpr R → (∀ i : Fin n, ArithVal R) → ArithVal R
  : ArithExpr Rat → (Fin n → R) → Option R
  | val x, _ => some <| RealLike.ofRat x
  | var i, vs => if h : i < n then vs ⟨i, h⟩ else none
  | neg e, vs => Option.map Neg.neg (interpret R e vs)
  | inv e, vs => Option.map Inv.inv (interpret R e vs)
  | srt e, vs => Option.map Srt.srt (interpret R e vs)
  | exp e, vs => Option.map Exp.exp (interpret R e vs)
  | log e, vs => Option.map Log.log (interpret R e vs)
  | add e₁ e₂, vs => Option.map2 Add.add (interpret R e₁ vs) (interpret R e₂ vs)
      -- match (interpret R e₁ Is), (interpret R e₂ Is) with 
      --   | scalar x, scalar y => scalar (x + y)
      --   | scalar x, vector n y => vector n (fun i => x + y i)
      --   | vector n x, scalar y => vector n (fun i => x i + y)
      --   | vector n x, vector m y => 
      --       if h : n = m then 
      --         vector n (fun i => x i + y (h ▸ i)) 
      --       else scalar 0
      --   | _, _ => scalar 0
  | mul e₁ e₂, vs => Option.map2 Mul.mul (interpret R e₁ vs) (interpret R e₂ vs)

instance : Min Rat where 
  min x y := if x < y then x else y

instance : Max Rat where 
  max x y := if x < y then y else x

def approx (R) [RealLike R] {n : Nat} (prec : Nat) 
  -- : ArithExpr Rat → (∀ i : Fin n, ArithVal (Interval? Rat)) → ArithVal (Interval? Rat)
  -- | val (scalar x), _ => scalar <| some ⟨x, x⟩
  -- | val (vector n x), _ => vector n <| fun i => some ⟨x i, x i⟩
  -- | val (matrix n m x), _ => matrix n m <| fun i j => some ⟨x i j, x i j⟩
  : ArithExpr Rat → (Fin n → Interval? Rat) → Interval? Rat
  | val x, _ => some ⟨x, x⟩
  | var i, Is => if h : i < n then Is ⟨i, h⟩ else none 
  | neg e, Is => arithBound R Neg.neg prec (approx R prec e Is)
  | inv e, Is => arithBound R Inv.inv prec (approx R prec e Is)
  | srt e, Is => arithBound R Srt.srt prec (approx R prec e Is)
  | exp e, Is => arithBound R Exp.exp prec (approx R prec e Is)
  | log e, Is => arithBound R Log.log prec (approx R prec e Is)
  | add e₁ e₂, Is => 
      match approx R prec e₁ Is, approx R prec e₂ Is with 
        | some I₁, some I₂ => some <| ⟨I₁.a + I₂.a, I₁.b + I₂.b⟩
        | _, _ => none 
  | mul e₁ e₂, Is => 
      match approx R prec e₁ Is, approx R prec e₂ Is with 
        | some I₁, some I₂ => 
            let ac := I₁.a * I₂.a
            let ad := I₁.a * I₂.b
            let bc := I₁.b * I₂.a
            let bd := I₁.b * I₂.b
            some <| ⟨min ac (min ad (min bc bd)), max ac (max ad (max bc bd))⟩
        | _, _ => none

def boundedVars {R} [RealLike R] {n : Nat} 
  (vs : Fin n → R) (Is : Fin n → Interval? Rat) : Prop := 
  ∀ i : Fin n, vs i ∈ Interval?.map (RealLike.ofRat (R := R)) (Is i)

theorem approx_correct (R) [RealLike R] {n : Nat} 
  (e : ArithExpr Rat) (vs : Fin n → R) (Is : Fin n → Interval? Rat)
  (prec : Nat) (h : boundedVars vs Is) 
  : if let some x := interpret R e vs then 
      x ∈ Interval?.map (RealLike.ofRat (R := R)) (approx R prec e Is)
    else True :=
  sorry
  --by induction e generalizing vs xs with
  

end ArithExpr
