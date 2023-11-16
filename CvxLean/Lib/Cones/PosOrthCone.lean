import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Matrix

namespace Real

def posOrthCone (x : Real) : Prop :=
  0 ≤ x

def Vec.posOrthCone (x : Fin n → Real) : Prop :=
  ∀ i, Real.posOrthCone (x i)

def Matrix.posOrthCone (M : Matrix (Fin m) (Fin n) Real) : Prop :=
  ∀ i j, Real.posOrthCone (M i j)

end Real
