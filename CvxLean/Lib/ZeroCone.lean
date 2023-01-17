import Mathbin.Data.Real.Basic

namespace Real 

def zeroCone (x : Real) : Prop :=
  x = 0

def Vec.zeroCone (x : Fin n → Real) : Prop := 
  ∀ i, Real.zeroCone (x i)

end Real 
