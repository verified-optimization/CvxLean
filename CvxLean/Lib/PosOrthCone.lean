import CvxLean.Lib.Missing.Mathlib

namespace Real 

def posOrthCone (x : ℝ) : Prop := 
  0 ≤ x

def Vec.posOrthCone (x : Finₓ n → ℝ) : Prop := 
  ∀ i, Real.posOrthCone (x i)

def Matrix.posOrthCone (M : Matrix (Finₓ m) (Finₓ n) ℝ) : Prop := 
  ∀ i j, Real.posOrthCone (M i j)

end Real 
