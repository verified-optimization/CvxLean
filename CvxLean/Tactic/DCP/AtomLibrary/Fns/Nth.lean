import CvxLean.Tactic.DCP.AtomCmd

/-!
Atoms for vector and matrix accesses (affine).
-/

namespace CvxLean

declare_atom Vec.nth [affine] (m : Nat)&  (x : Fin m → ℝ)? (i : Fin m)& : x i :=
bconditions
homogenity by
  rw [Pi.zero_apply]
  change _ * _ + _ = _ * _ + _ * _
  ring
additivity by
  rw [Pi.zero_apply]
  change _ + _ = _ + _ + _
  ring
optimality le_refl _

declare_atom Matrix.nth [affine] (m : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)? (i : Fin m)& :
  X i :=
bconditions
homogenity by
  rw [Pi.zero_apply, add_zero, smul_zero, add_zero]
  rfl
additivity by
  rw [Pi.zero_apply, add_zero]
  rfl
optimality le_refl _

declare_atom Matrix.nth2 [affine] (m : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)? (i : Fin m)&
  (j : Fin m)& : X i j :=
bconditions
homogenity by
  rw [Pi.zero_apply, Pi.zero_apply, smul_zero]
  rfl
additivity by
  rw [Pi.zero_apply, Pi.zero_apply, add_zero]
  rfl
optimality le_refl _

end CvxLean
