import CvxLean.Lib.Missing.Mathlib

namespace Real 

def zeroCone (x : ℝ) : Prop :=
  x = 0

def Vec.zeroCone (x : Fin n → ℝ) : Prop := 
  ∀ i, Real.zeroCone (x i)

end Real 
