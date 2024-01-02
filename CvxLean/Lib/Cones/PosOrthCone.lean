/-
Copyright (c) 2024 Verified Optimization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Ramon Fernández Mir
-/
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Matrix

namespace Real

/-- The positive (actually, nonnegative) orthant
      `ℝ₊ := { x | 0 ≤ x } ⊆ ℝ`. -/
def posOrthCone (x : ℝ) : Prop :=
  0 ≤ x

/-- The `n`-dimensional positive orthant `ℝ₊ⁿ`. -/
def Vec.posOrthCone {n} [Fintype n] (x : n → ℝ) : Prop :=
  ∀ i, Real.posOrthCone (x i)

/-- The `n×m`-dimensional positive orthant `ℝ₊ⁿˣᵐ`. -/
def Matrix.posOrthCone {n m} [Fintype n] [Fintype m] (M : Matrix n m ℝ) :
  Prop :=
  ∀ i j, Real.posOrthCone (M i j)

end Real
