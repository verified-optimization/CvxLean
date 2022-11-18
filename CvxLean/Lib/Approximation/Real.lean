import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Approximation.DyadicExpr 

-- TODO: wrong, negative case.
noncomputable def Lean.Rat.toReal (x : Lean.Rat) : Real :=  
  (x.num.natAbs : Real) / (x.den : Real)

lemma sqrtRatIter_correct (x : Lean.Rat) : 
  Real.sqrt x.toReal < (sqrtRatIter n prec x).toReal := by 
  induction n with 
  | zero => 
      simp only [sqrtRatIter, Lean.Rat.toReal]
      sorry
  | succ n ih => sorry

-- lemma sqrtRat_correct (x : Real) : 
--   sqrtRatUp prec x ≤ sqrt x ∧ sqrt x ≤ sqrtRatDown prec x := by 
--   sorry 

class RealLike (α) extends Neg α, Inv α, Add α, Mul α, LE α where
  sqrt : α → α
  exp : α → α
  log : α → α
  pow : α → Nat → α
  ofDyadic : Dyadic → α
  ofDyadic_eq : ∀ x y, (ofDyadic x = ofDyadic y) ↔ (x = y)
  ofDyadic_le : ∀ x y, (ofDyadic x ≤ ofDyadic y) ↔ (x ≤ y)

noncomputable def Real.ipow (x : Real) (p : Int) : Real := 
  if p ≥ 0 then x ^ p.natAbs
  else 1 / (x ^ (-p).natAbs)

noncomputable def Dyadic.toReal (x : Dyadic) : Real := 
  (@CommRingₓ.intCast Real _ x.m) * (Real.ipow 2 x.e)

theorem Dyadic.toRealOfNat (x : Nat) : Dyadic.toReal (OfNat.ofNat x) = x :=
  sorry

theorem Dyadic.toReal_le (x y : Dyadic) : (x.toReal ≤ y.toReal) ↔ (x ≤ y) := 
  sorry

namespace DyadicExpr

noncomputable def interpret : DyadicExpr → List Real → Real
  | num x,     _  => x.toReal
  | var i,     xs => xs.get! i
  | neg e,     xs => -(interpret e xs)
  | inv e,     xs => (interpret e xs)⁻¹
  | sqrt e,    xs => (interpret e xs).sqrt
  | exp e,     xs => (interpret e xs).exp
  | log e,     xs => (interpret e xs).log
  | pow e p,   xs => (interpret e xs) ^ p
  | add e₁ e₂, xs => (interpret e₁ xs) + (interpret e₂ xs)
  | mul e₁ e₂, xs => (interpret e₁ xs) * (interpret e₂ xs)

def boundedBy (x : Real) (I : Interval Dyadic) : Prop := 
  I.a.toReal ≤ x ∧ x ≤ I.b.toReal

def boundedByOpt (x : Real) : Option (Interval Dyadic) → Prop
  | none => True -- ???
  | some I => boundedBy x I

def boundedByList (xs : List Real) (Is : List (Option (Interval Dyadic))) : Prop := 
  xs.length = Is.length ∧ 
  ∀ i (hxs : Nat.lt i xs.length) (hIs : Nat.lt i Is.length), 
    boundedByOpt (xs.get ⟨i, hxs⟩) (Is.get ⟨i, hIs⟩)

open Interval

#check Lean.Rat

theorem approx_correct (prec : Nat) 
  (e : DyadicExpr) (xs : List Real) (vs : List (Option (Interval Dyadic))) 
  (hbounded : boundedByList xs vs) :
  if let some I := e.approx prec vs then 
    boundedBy (e.interpret xs) I
  else True := by 
  induction e generalizing vs xs with 
  | num x => simp only [approx, interpret, boundedBy, le_reflₓ] 
  | var i => sorry
  | neg e ih => 
      have ih' := ih xs vs hbounded
      revert ih'
      simp only [approx]
      cases (approx prec e vs) with 
      | none => simp only [Option.bind]
      | some I => 
          simp only [Option.bind, interpret, boundedBy]
          intros h 
          sorry
          --exact (ih xs vs hbounded)
  | inv e => sorry
  | sqrt e => sorry
  | exp e => sorry
  | log e => sorry
  | pow e p => sorry
  | add e₁ e₂ => sorry
  | mul e₁ e₂ => sorry

end DyadicExpr

namespace ArithForm

def interpret : ArithForm → List Real → Prop 
  | le e₁ e₂,  xs => (e₁.interpret xs) ≤ (e₂.interpret xs)
  | and e₁ e₂, xs => (interpret e₁ xs) ∧ (interpret e₂ xs)

theorem approx_correct (prec : Nat)
  (f : ArithForm) (xs : List Real) (vs : List (Option (Interval Dyadic))) 
  (hbounded : DyadicExpr.boundedByList xs vs) 
  (happrox : f.approx prec vs) :
  f.interpret xs := by 
  induction f generalizing vs xs with
  | le e₁ e₂ => 
      have h₁ := DyadicExpr.approx_correct prec e₁ xs vs hbounded
      have h₂ := DyadicExpr.approx_correct prec e₂ xs vs hbounded
      revert h₁ h₂
      revert happrox
      simp only [approx]
      match DyadicExpr.approx prec e₁ vs with 
      | some I₁ => 
          dsimp
          match DyadicExpr.approx prec e₂ vs with 
          | some I₂ => 
              dsimp 
              simp only [DyadicExpr.boundedBy]
              intros happrox h₁ h₂ 
              simp only [interpret]
              sorry
          | none => dsimp; intros hf; contradiction
      | none => dsimp; intros hf; contradiction
      
  | and => sorry

end ArithForm
