import CvxLean.Tactic.DCP.AtomCmdimport CvxLean.Lib.Math.Data.Matrix

namespace CvxLean

declare_atom Matrix.const [affine] (m : Type)& (n : Type)& (k : ℝ)& :
    Matrix.const (m := m) (n := n) k :=
bconditions
homogenity by
  ext; simp [Matrix.const]; ring
additivity by
  simp [Matrix.mul_add]
optimality le_refl _

end CvxLean
