/-
Copyright (c) 2024 Verified Optimization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Ramon Fernández Mir
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Real

/-- The cone of `n×n` positive semidefinite matrices
      `𝒮₊ⁿ := { A | A is symmetric ∧ 0 ≼ A } ⊆ ℝⁿˣⁿ`. -/
def Matrix.PSDCone {n} [Fintype n] (A : Matrix n n ℝ) : Prop :=
  Matrix.PosSemidef A

end Real
