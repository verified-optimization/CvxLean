import FFI
import Mathbin.Data.Real.Sqrt

noncomputable def Real.ofRat (x : Rat) : Real := 
  if x.num < 0 then -1 else 1 * (x.num.natAbs : Real) / (x.den : Real)

axiom Ball.sqrt_correct : ∀ (prec : Nat) (b : Ball Rat), 
  b.map (Real.sqrt ∘ Real.ofRat) ⊆ (Ball.sqrt prec b).map Real.ofRat
