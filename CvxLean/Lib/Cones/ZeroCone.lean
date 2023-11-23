import Mathlib.Data.Real.Basic
import CvxLean.Lib.Math.Data.Matrix

namespace Real

@[irreducible]
def zeroCone (x : Real) : Prop :=
  x = 0

@[irreducible]
def Vec.zeroCone (x : Fin n → Real) : Prop :=
  ∀ i, Real.zeroCone (x i)

@[irreducible]
def Matrix.zeroCone (M : Matrix (Fin n) (Fin m) Real) : Prop :=
  ∀ i j, Real.zeroCone (M i j)

end Real
