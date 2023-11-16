import CvxLean.Tactic.DCP.Atoms

namespace CvxLean

theorem Matrix.vecCons_zero_zero {n}
  : Matrix.vecCons (0 : ℝ) (0 : Fin n → ℝ) = 0 := by
  ext i ; refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]

theorem Matrix.smul_vecCons {n} (x : ℝ) (y : ℝ) (v : Fin n → ℝ)
  : x • Matrix.vecCons y v = Matrix.vecCons (x • y) (x • v) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]

theorem Matrix.add_vecCons {n} (x : ℝ) (v : Fin n → ℝ) (y : ℝ) (w : Fin n → ℝ)
  : Matrix.vecCons x v + Matrix.vecCons y w = Matrix.vecCons (x + y) (v + w) := by
  ext i ; refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]

declare_atom Matrix.vec_cons [affine] (n : Nat)& (x : ℝ)+ (y : (Fin n) → ℝ)+ :
  Matrix.vecCons x y :=
bconditions
homogenity by
  simp only [Matrix.vecCons_zero_zero, smul_zero, add_zero, Matrix.smul_vecCons]
additivity by
  simp only [Matrix.add_vecCons, add_zero]
optimality by
  intros x' y' hx hy i
  refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]
  . exact hx
  . exact hy

end CvxLean
