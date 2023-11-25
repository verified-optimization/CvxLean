import Mathlib.Data.Real.Basic
import CvxLean.Lib.Math.Data.Matrix

namespace Real

def zeroCone (x : Real) : Prop :=
  x = 0

def Vec.zeroCone (x : Fin n → Real) : Prop :=
  ∀ i, Real.zeroCone (x i)

def Matrix.zeroCone (M : Matrix (Fin n) (Fin m) Real) : Prop :=
  ∀ i j, Real.zeroCone (M i j)

end Real
