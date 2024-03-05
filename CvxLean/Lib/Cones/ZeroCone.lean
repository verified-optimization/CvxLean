import Mathlib.Data.Real.Basic
import CvxLean.Lib.Math.Data.Matrix

/-!
Zero cones.
-/

namespace Real

/-- The zero cone `{0}`. -/
def zeroCone (x : ℝ) : Prop :=
  x = 0

/-- The `n`-dimensional zero cone `{0}ⁿ`. -/
def Vec.zeroCone {n} [Fintype n] (x : n → ℝ) : Prop :=
  ∀ i, Real.zeroCone (x i)

/-- The `n×m`-dimensional zero cone `{0}ⁿˣᵐ`. -/
def Matrix.zeroCone {n m} [Fintype n] [Fintype m] (M : Matrix n m ℝ) : Prop :=
  ∀ i j, Real.zeroCone (M i j)

end Real
