import CvxLean.Lib.Approximation.Dyadic 
import CvxLean.Lib.Approximation.Interval 

inductive DyadicExpr 
  | num   : Dyadic → DyadicExpr
  | var   : Nat → DyadicExpr
  | neg   : DyadicExpr → DyadicExpr
  | inv   : DyadicExpr → DyadicExpr
  | sqrt  : DyadicExpr → DyadicExpr
  | exp   : DyadicExpr → DyadicExpr
  | log   : DyadicExpr → DyadicExpr
  | pow   : DyadicExpr → Nat → DyadicExpr
  | add   : DyadicExpr → DyadicExpr → DyadicExpr
  | mul   : DyadicExpr → DyadicExpr → DyadicExpr

#check Inv

namespace DyadicExpr 

def sub (e₁ e₂ : DyadicExpr) : DyadicExpr := 
  DyadicExpr.add e₁ (DyadicExpr.neg e₂)

def div (e₁ e₂ : DyadicExpr) : DyadicExpr := 
  DyadicExpr.mul e₁ (DyadicExpr.inv e₂)

def approx (prec : Nat) 
  : DyadicExpr → List (Option (Interval Dyadic)) → (Option (Interval Dyadic))
  | num x,     _  => Interval.mk x x
  | var i,     xs => if h : i < xs.length then xs.get ⟨i, h⟩ else none
  | neg e,     xs => Option.bind (approx prec e xs) (fun x => Interval.mk (-x.b) (-x.a))
  | inv e,     xs => none 
  | sqrt e,    xs => none 
  | exp e,     xs => none
  | log e,     xs => none 
  | pow e p,   xs => none
  | add e₁ e₂, xs => none 
  | mul e₁ e₂, xs => none

end DyadicExpr

inductive ArithForm 
  | le : DyadicExpr → DyadicExpr → ArithForm
  | and : ArithForm → ArithForm → ArithForm

namespace ArithForm

def approx (prec : Nat) 
  : ArithForm → List (Option (Interval Dyadic)) → Prop
  | le e₁ e₂, xs => match 
      (DyadicExpr.approx prec e₁ xs, DyadicExpr.approx prec e₂ xs) with
    | (some I₁, some I₂) => Dyadic.roundUp prec I₁.b ≤ Dyadic.roundDown prec I₂.a
    | _ => False
  | and f₁ f₂, xs => approx prec f₁ xs ∧ approx prec f₂ xs

end ArithForm

