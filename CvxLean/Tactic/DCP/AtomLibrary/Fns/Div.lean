import CvxLean.Tactic.DCP.AtomCmd

/-!
Division atom (affine).
-/

namespace CvxLean

open Real

declare_atom div [affine] (x : ℝ)+ (y : ℝ)& : x / y :=
bconditions (hy : (0 : ℝ) ≤ y)
homogenity by
  simp [mul_div]
additivity by
  simp [add_div]
optimality by
  intros x' hx
  by_cases h : 0 = y
  · rw [← h, div_zero, div_zero]
  · rw [div_le_div_right]
    apply hx
    apply lt_of_le_of_ne hy h

end CvxLean
