import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Approximation.DyadicExpr 

noncomputable def Real.ipow (x : Real) (p : Int) : Real := 
  if p ≥ 0 then x ^ p.natAbs
  else 1 / (x ^ (-p).natAbs)

noncomputable def Dyadic.toReal (x : Dyadic) : Real := 
  (@CommRingₓ.intCast Real _ x.m) * (Real.ipow 2 x.e)

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
  xs.length = Is.length ∧ ∀ i, boundedByOpt (xs.get! i) (Is.get! i)

open Interval

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

open Lean

def crazy (e : Expr) : Option DyadicExpr := 
  match e with 
  | Expr.app (Expr.app (Expr.app (Expr.const `Nat.cast _) _) _) n => 
      match n with 
      | Expr.lit (Literal.natVal n) => some (DyadicExpr.num n)
      | _ => none
  -- | Expr.app (Expr.app (Expr.const `Add.Add _) e₁) e₂ => 
  --   match crazy e₁, crazy e₂ with 
  --   | some e₁, some e₂ => some (DyadicExpr.add e₁ e₂)
  --   | _, _ => none
  | _ => none

def crazy2 (r : Real) : Option DyadicExpr := sorry


def crazy3 (r : Real) : MetaM (Option DyadicExpr) := sorry

/-
Basically every atom will need a translation to 
-/

#check Meta.inferType

axiom correct : ∀ (r : Real), 
  if let some de := crazy2 r then 
    DyadicExpr.interpret de [] = r
  else True
