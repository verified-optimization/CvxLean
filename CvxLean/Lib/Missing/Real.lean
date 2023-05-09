import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential

namespace Real

def log (x : Real) : Real := 
  sorry

macro "π" : term => 
  `(Real.pi)

noncomputable instance : OfScientific Real := {
  ofScientific := fun mantissa exponentSign decimalExponent => 
    if exponentSign
    then mantissa / (10 ^ decimalExponent)
    else mantissa * (10 ^ decimalExponent)
}

noncomputable def entr (x : Real) := 
  -(x * Real.log x)

noncomputable def huber (x : Real) := 
  if abs x ≤ 1
  then x ^ 2
  else 2 * abs x - 1

noncomputable def kl_div (x y : Real) :=
  x * log (x / y) - x + y

end Real
