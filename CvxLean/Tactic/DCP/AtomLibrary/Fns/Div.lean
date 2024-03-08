import CvxLean.Tactic.DCP.AtomCmd

/-!
Division atom (affine).
-/

namespace CvxLean

open Real

declare_atom div1 [affine] (x : ℝ)+ (y : ℝ)& : x / y :=
bconditions
  (hy : 0 ≤ y)
homogenity by
  simp [mul_div]
additivity by
  simp [add_div]
optimality by
  intros x' hx
  by_cases h : 0 = y
  · rw [← h, div_zero, div_zero]
  · rw [div_le_div_right (lt_of_le_of_ne hy h)]
    apply hx

declare_atom div2 [affine] (x : ℝ)- (y : ℝ)& : x / y :=
bconditions
  (hy : y ≤ 0)
homogenity by
  simp [mul_div]
additivity by
  simp [add_div]
optimality by
  intros x' hx
  by_cases h : y = 0
  · rw [h, div_zero, div_zero]
  · rw [div_le_div_right_of_neg (lt_of_le_of_ne hy h)]
    apply hx

end CvxLean
