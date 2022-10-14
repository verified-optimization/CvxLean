import Mathbin.Data.Real.Basic
import Mathbin.Data.Complex.Exponential
import Mathbin.Analysis.SpecialFunctions.Log.Basic
import CvxLean.Lib.Missing.Mathlib
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Group.Defs

attribute [-instance] coeDecidableEq

namespace Real

macro "π" : term => 
  do return Lean.TSyntax.raw (← `(Real.pi))

variable (x y : ℝ)

noncomputable instance : AddMonoidWithOne Real := { 
  one := Real.hasOne.one,
  add_assoc := add_assocₓ,
  add_zero := add_zeroₓ,
  zero_add := zero_addₓ,
  nsmul_zero' := AddMonoidWithOneₓ.nsmul_zero',
  nsmul_succ' := AddMonoidWithOneₓ.nsmul_succ',
  natCast := AddMonoidWithOneₓ.natCast,
  natCast_zero := AddMonoidWithOneₓ.nat_cast_zero,
  natCast_succ := AddMonoidWithOneₓ.nat_cast_succ
}

noncomputable instance : MonoidWithZero Real := {
  zero := Real.hasZero.zero,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  mul_assoc := Monoidₓ.mul_assoc,
  mul_one := Monoidₓ.mul_one,
  one_mul := Monoidₓ.one_mul,
  npow_zero' := Monoidₓ.npow_zero',
  npow_succ' := Monoidₓ.npow_succ'
}

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
