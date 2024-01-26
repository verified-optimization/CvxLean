import CvxLean

noncomputable section

namespace FittingSphere

open CvxLean Minimization Real BigOperators Matrix

-- Dimension.
variable (n : ℕ)

-- Number of points.
variable (m : ℕ)

-- Given points.
variable (x : Fin m → Fin n → ℝ)

def fittingSphere :=
  optimization (c : Fin n → ℝ) (r : ℝ)
    minimize (∑ i, (‖(x i) - c‖ ^ 2 - r ^ 2) ^ 2 : ℝ)

#print fittingSphere

equivalence eqv/fittingSphereConvex (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere n m x := by
  equivalence_rfl


end FittingSphere

end
