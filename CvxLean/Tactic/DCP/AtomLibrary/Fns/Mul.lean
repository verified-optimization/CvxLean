import CvxLean.Tactic.DCP.AtomCmd

/-!
Multiplication atoms (affine).
-/

namespace CvxLean

declare_atom mul1 [affine] (x : ℝ)& (y : ℝ)+ : x * y :=
bconditions (hx : 0 ≤ x)
homogenity by
  simp; ring
additivity by
  ring
optimality by
  intros y' hy
  apply mul_le_mul_of_nonneg_left hy hx

declare_atom mul2 [affine] (x : ℝ)+ (y : ℝ)& : x * y :=
bconditions (hy : 0 ≤ y)
homogenity by
  simp; ring
additivity by
  ring
optimality by
  intros y' hx
  apply mul_le_mul_of_nonneg_right hx hy

declare_atom mul3 [affine] (x : ℝ)& (y : ℝ)- : x * y :=
bconditions (hx : x ≤ 0)
homogenity by
  simp; ring
additivity by
  ring
optimality by
  intros y' hy
  apply mul_le_mul_of_nonpos_left hy hx

declare_atom mul4 [affine] (x : ℝ)- (y : ℝ)& : x * y :=
bconditions (hy : y ≤ 0)
homogenity by
  simp; ring
additivity by
  ring
optimality by
  intros y' hx
  apply mul_le_mul_of_nonpos_right hx hy

declare_atom Vec.mul1 [affine] (n : ℕ)& (x : Fin n → ℝ)& (y : Fin n → ℝ)+ : x * y :=
bconditions (hx : 0 ≤ x)
homogenity by
  funext i; dsimp; simp; ring
additivity by
  ring
optimality by
  intros y' hy
  apply mul_le_mul_of_nonneg_left hy hx

declare_atom Vec.mul2 [affine] (n : ℕ)& (x : Fin n → ℝ)+ (y : Fin n → ℝ)& : x * y :=
bconditions (hy : 0 ≤ y)
homogenity by
  funext i; dsimp; simp; ring
additivity by
  ring
optimality by
  intros y' hx
  apply mul_le_mul_of_nonneg_right hx hy

declare_atom Vec.mul3 [affine] (n : ℕ)& (x : Fin n → ℝ)& (y : Fin n → ℝ)- : x * y :=
bconditions (hx : x ≤ 0)
homogenity by
  funext i; dsimp; simp; ring
additivity by
  ring
optimality by
  intros y' hy
  apply mul_le_mul_of_nonpos_left hy hx

declare_atom Vec.mul4 [affine] (n : ℕ)& (x : Fin n → ℝ)- (y : Fin n → ℝ)& : x * y :=
bconditions (hy : y ≤ 0)
homogenity by
  funext i; dsimp; simp; ring
additivity by
  ring
optimality by
  intros y' hx
  apply mul_le_mul_of_nonpos_right hx hy

end CvxLean
