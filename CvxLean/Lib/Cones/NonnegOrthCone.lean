import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Matrix

namespace Real

/-- The nonnegative orthant
      `ℝ₊ := { x | 0 ≤ x } ⊆ ℝ`. -/
def nonnegOrthCone (x : ℝ) : Prop :=
  0 ≤ x

/-- The `n`-dimensional nonnegative orthant `ℝ₊ⁿ`. -/
def Vec.nonnegOrthCone {n} [Fintype n] (x : n → ℝ) : Prop :=
  ∀ i, Real.nonnegOrthCone (x i)

/-- The `n×m`-dimensional nonnegative orthant `ℝ₊ⁿˣᵐ`. -/
def Matrix.nonnegOrthCone {n m} [Fintype n] [Fintype m] (M : Matrix n m ℝ) :
  Prop :=
  ∀ i j, Real.nonnegOrthCone (M i j)

end Real
