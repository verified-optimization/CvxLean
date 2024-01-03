import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Real

/-- The cone of `n×n` positive semidefinite matrices
      `𝒮₊ⁿ := { A | A is symmetric ∧ 0 ≼ A } ⊆ ℝⁿˣⁿ`. -/
def Matrix.PSDCone {n} [Fintype n] (A : Matrix n n ℝ) : Prop :=
  Matrix.PosSemidef A

end Real
