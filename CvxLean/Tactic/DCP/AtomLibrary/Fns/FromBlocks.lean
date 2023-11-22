import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

open Matrix

declare_atom Matrix.fromBlocks [affine] (n : ℕ)&
  (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+
  (B : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+
  (C : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+
  (D : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ :
  fromBlocks A B C D :=
bconditions
homogenity by
  rw [fromBlocks_zero, smul_zero, add_zero, add_zero, fromBlocks_smul]
additivity by
  simp [fromBlocks_add]
optimality by
  intros A' B' C' D' hA hB hC hD i j
  cases i <;> cases j <;> simp [fromBlocks]
  . exact hA _ _
  . exact hB _ _
  . exact hC _ _
  . exact hD _ _

end CvxLean
