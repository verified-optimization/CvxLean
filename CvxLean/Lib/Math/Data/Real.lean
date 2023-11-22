import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real

noncomputable def entr (x : Real) :=
  -(x * Real.log x)

noncomputable def huber (x : Real) :=
  if abs x ≤ 1 then x ^ 2 else 2 * abs x - 1

noncomputable def klDiv (x y : Real) :=
  x * log (x / y) - x + y

end Real
