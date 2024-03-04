import CvxLean.Tactic.DCP.AtomCmd
import CvxLean.Lib.Cones.All
import CvxLean.Syntax.Minimization

namespace CvxLean

open Real

/- Zero cone atom. -/
section ZeroCone

declare_atom zeroCone [cone] (x : ℝ)? : zeroCone x :=
optimality by
  simp [zeroCone]

end ZeroCone

/- Nonnegative orthant cone atoms. -/
section NonnegOrthCone

declare_atom nonnegOrthCone [cone] (x : ℝ)? : nonnegOrthCone x :=
optimality by
  simp [nonnegOrthCone]

declare_atom Vec.nonnegOrthCone [cone]
  (n : Nat)& (x : (Fin n) → ℝ)? : Vec.nonnegOrthCone x :=
optimality by
  simp [Vec.nonnegOrthCone]

declare_atom Matrix.nonnegOrthCone [cone]
  (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)? :
  Real.Matrix.nonnegOrthCone M :=
optimality by
  simp [Matrix.nonnegOrthCone]

end NonnegOrthCone

/- Exponential cone atoms. -/
section ExpCone

declare_atom expCone [cone] (x : ℝ)? (y : ℝ)? (z : ℝ)? : expCone x y z :=
optimality le_refl _

declare_atom Vec.expCone [cone] (n : Nat)& (x : (Fin n) → ℝ)? (y : (Fin n) → ℝ)?
  (z : (Fin n) → ℝ)? : Vec.expCone x y z :=
optimality le_refl _

end ExpCone

/- Second-order cone and rotated second-order cone atoms. -/
section SOCone

declare_atom soCone [cone] (n : Nat)& (t : ℝ)? (x : (Fin n) → ℝ)? :
  soCone t x :=
optimality le_refl _

declare_atom Vec.soCone [cone] (n : Nat)& (m : Nat)& (t : Fin m → Real)?
  (X : Matrix.{0,0,0} (Fin m) (Fin n) Real)? : Vec.soCone t X :=
optimality le_refl _

declare_atom rotatedSoCone [cone] (n : Nat)& (v : ℝ)? (w : ℝ)?
  (x : (Fin n) → ℝ)? : rotatedSoCone v w x :=
optimality le_refl _

declare_atom Vec.rotatedSoCone [cone] (m : Nat)& (n : Nat)& (v : (Fin n) → ℝ)?
  (w : (Fin n) → ℝ)? (x : (Fin n) → (Fin m) → ℝ)? : Vec.rotatedSoCone v w x :=
optimality le_refl _

end SOCone

/- Positive semi-definite cone atom. -/
section PSDCone

declare_atom Matrix.PSDCone [cone] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)? : Matrix.PSDCone A :=
optimality le_refl _

end PSDCone

/- Trivial cone atom. -/
section Trivial

declare_atom trivial [cone] : True :=
optimality le_refl _

end Trivial

end CvxLean
