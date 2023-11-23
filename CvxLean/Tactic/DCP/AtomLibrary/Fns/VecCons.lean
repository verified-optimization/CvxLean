import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

open Matrix

declare_atom vecCons [affine] (n : Nat)& (x : ℝ)+ (y : (Fin n) → ℝ)+ :
  vecCons x y :=
bconditions
homogenity by
  simp only [vecCons_zero_zero, smul_zero, add_zero, smul_vecCons]
additivity by
  simp only [add_vecCons, add_zero]
optimality by
  intros x' y' hx hy i
  refine' Fin.cases _ _ i <;> simp [vecCons]
  . exact hx
  . exact hy

end CvxLean
