import Mathbin.Data.Real.Basic
import Mathbin.Data.Complex.Exponential
import Mathbin.Analysis.SpecialFunctions.Log.Basic
import CvxLean.Lib.Missing.Mathlib
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Group.Defs

attribute [-instance] coeDecidableEq

namespace Real

macro "π" : term => 
  `(Real.pi)

variable (x y : Real)

noncomputable instance : Preorder Real := by infer_instance

noncomputable instance : AddMonoidWithOne Real := by infer_instance

noncomputable instance : MonoidWithZero Real := by infer_instance

noncomputable instance : OfScientific Real := {
  ofScientific := fun mantissa exponentSign decimalExponent => 
    if exponentSign
    then mantissa / (10 ^ decimalExponent)
    else mantissa * (10 ^ decimalExponent)
}

noncomputable def entr := 
  -(x * Real.log x)

noncomputable def huber := 
  if abs x ≤ 1
  then x ^ 2
  else 2 * abs x - 1

noncomputable def kl_div :=
  x * log (x / y) - x + y

end Real
