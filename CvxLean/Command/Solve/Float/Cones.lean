import CvxLean.Lib.Math.Data.Matrix

namespace Float

-- TODO: Is this needed?

def zeroCone (x : Float) : Prop :=
  x = 0

def Vec.zeroCone (x : Fin n → Float) : Prop :=
  ∀ i, Float.zeroCone (x i)

def posOrthCone (x : Float) : Prop :=
  x ≤ 0

def Vec.posOrthCone (x : Fin n → Float) : Prop :=
  ∀ i, Float.posOrthCone (x i)

def Matrix.posOrthCone (M : Matrix (Fin n) (Fin m) Float) : Prop :=
  ∀ i j, Float.posOrthCone (M i j)

def expCone (x y z : Float) : Prop :=
  (0 < y ∧ y * exp (x / y) ≤ z) ∨ (y = 0 ∧ 0 ≤ z ∧ x ≤ 0)

def Vec.expCone (x y z : Fin n → Float) : Prop :=
  ∀ i, Float.expCone (x i) (y i) (z i)

def Matrix.PSDCone (M : Matrix (Fin n) (Fin n) Float) : Prop :=
  Matrix.Computable.PosSemidef M

end Float
