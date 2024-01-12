import CvxLean.Lib.Math.Data.Matrix

namespace Float

def zeroCone (x : Float) : Prop :=
  x = 0

def Vec.zeroCone {n} [Fintype n] (x : n → Float) : Prop :=
  ∀ i, Float.zeroCone (x i)

def posOrthCone (x : Float) : Prop :=
  x ≤ 0

def Vec.posOrthCone {n} [Fintype n] (x : n → Float) : Prop :=
  ∀ i, Float.posOrthCone (x i)

def Matrix.posOrthCone {n m} [Fintype n] [Fintype m] (M : Matrix n m Float) : Prop :=
  ∀ i j, Float.posOrthCone (M i j)

def expCone (x y z : Float) : Prop :=
  (0 < y ∧ y * exp (x / y) ≤ z) ∨ (y = 0 ∧ 0 ≤ z ∧ x ≤ 0)

def Vec.expCone {n} [Fintype n] (x y z : n → Float) : Prop :=
  ∀ i, Float.expCone (x i) (y i) (z i)

def Matrix.PSDCone {n} (M : Matrix (Fin n) (Fin n) Float) : Prop :=
  Matrix.Computable.PosSemidef M

end Float
