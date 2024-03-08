import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Math.Data.Vec

/-!
Atom for making a constant vector (affine).
-/

namespace CvxLean

open Real

declare_atom Vec.const [affine] (n : Nat)& (x : ℝ)? :
  Vec.const n x :=
bconditions
homogenity by
  unfold Vec.const; ext; simp
additivity by
  unfold Vec.const; ext; simp
optimality le_refl _

end CvxLean
