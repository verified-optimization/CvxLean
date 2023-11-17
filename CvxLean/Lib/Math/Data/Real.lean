import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real

noncomputable def entr (x : Real) :=
  -(x * Real.log x)

noncomputable def huber (x : Real) (M : Real) :=
  if abs x ≤ M
  then x ^ 2
  else 2 * M * abs x - M ^ 2

noncomputable def klDiv (x y : Real) :=
  x * log (x / y) - x + y

end Real
