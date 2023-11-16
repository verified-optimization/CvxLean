import CvxLean.Tactic.DCP.Atoms
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

/- Positive orthant cone atoms. -/
section PosOrthCone

declare_atom posOrthCone [cone] (x : ℝ)? : posOrthCone x :=
optimality by
  simp [posOrthCone]

declare_atom Vec.posOrthCone [cone]
  (n : Nat)& (x : (Fin n) → ℝ)? : Vec.posOrthCone x :=
optimality by
  simp [Vec.posOrthCone]

declare_atom Matrix.posOrthCone [cone]
  (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)? :
  Real.Matrix.posOrthCone M :=
optimality by
  simp [Matrix.posOrthCone]

end PosOrthCone

/- Exponential cone atoms. -/
section ExpCone

declare_atom expCone [cone] (x : ℝ)- (y : ℝ)? (z : ℝ)+ : expCone x y z :=
optimality by
  intros x' z' hx hz hexp
  simp only [expCone] at hexp ⊢
  cases hexp with
  | inl hexp => {
      left
      rcases hexp with ⟨hy, hexp⟩
      apply And.intro hy;
      refine' le_trans _ (le_trans hexp hz);
      refine' mul_le_mul_of_nonneg_left _ _;
      { rw [exp_le_exp];
        refine' (div_le_div_right _).2 hx;
        exact hy }
      { apply le_of_lt;
        exact hy } }
  | inr hyzx => {
      right
      rcases hyzx with ⟨hy, h0z, hx0⟩
      apply And.intro hy;
      exact ⟨le_trans h0z hz, le_trans hx hx0⟩ }

declare_atom Vec.expCone [cone] (n : Nat)& (x : (Fin n) → ℝ)- (y : (Fin n) → ℝ)?
  (z : (Fin n) → ℝ)+ : Vec.expCone x 1 z :=
optimality by
  intros x' z' hx hz hexp i
  exact expCone.optimality (hx := hx i) (hz := hz i) (hexp := hexp i)

end ExpCone

/- Second-order cone and rotated second-order cone atoms. -/
section SOCone

declare_atom soCone [cone] (n : Nat)& (t : ℝ)+ (x : (Fin n) → ℝ)? :
  soCone t x :=
optimality by
  intros t' ht h
  exact le_trans h ht

declare_atom Vec.soCone [cone] (n : Nat)& (m : Nat)& (t : Fin m → Real)+
  (X : Matrix.{0,0,0} (Fin m) (Fin n) Real)? : Vec.soCone t X :=
optimality by
  intros t' ht h i
  exact soCone.optimality (ht := ht i) (h := h i)

declare_atom rotatedSoCone [cone] (n : Nat)& (v : ℝ)+ (w : ℝ)+
  (x : (Fin n) → ℝ)? : rotatedSoCone v w x :=
optimality by
  intros v' w' hv hw h
  unfold rotatedSoCone at *
  apply And.intro
  · apply h.1.trans
    apply mul_le_mul_of_nonneg_right
    apply mul_le_mul_of_le_of_le hv hw h.2.1 (h.2.2.trans hw)
    norm_num
  · exact ⟨h.2.1.trans hv, h.2.2.trans hw⟩

declare_atom Vec.rotatedSoCone [cone] (m : Nat)& (n : Nat)& (v : (Fin n) → ℝ)+
  (w : (Fin n) → ℝ)+ (x : (Fin n) → (Fin m) → ℝ)? : Vec.rotatedSoCone v w x :=
optimality by
  intros v' w' hv hw h i
  exact rotatedSoCone.optimality (hv := hv i) (hw := hw i) (h := h i)

end SOCone

/- Positive semi-definite cone atom. -/
section PSDCone

declare_atom Matrix.PSDCone [cone] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)? : Matrix.PSDCone A :=
optimality fun h => h

end PSDCone

end CvxLean
