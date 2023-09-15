import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Cones
import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Missing.Vec
import CvxLean.Lib.Missing.Matrix
import CvxLean.Lib.Optlib.LogDet
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.LDL
import CvxLean.Syntax.Minimization

namespace CvxLean

-- Constraints in conic form.
section Cones

open Real

declare_atom expCone [cone] (x : ℝ)- (z : ℝ)+ : expCone x 1 z :=
optimality by
  intros x' z' hx hz hexp
  rw [←exp_iff_expCone] at *
  have hexpleexp := exp_le_exp.2 hx
  exact (hexpleexp.trans hexp).trans hz

declare_atom expCone2 [cone] (x : ℝ)- (y : ℝ)? (z : ℝ)+ : expCone x y z :=
optimality by
  intros x' z' hx hz hexp
  simp only [expCone] at hexp ⊢
  cases hexp with
  | inl hexp => {
      left 
      rcases hexp with ⟨hy, hexp⟩
      apply And.intro hy;
      refine' le_transₓ _ (le_transₓ hexp hz);
      refine' ZeroLt.mul_le_mul_of_nonneg_left _ _;
      { rw [exp_le_exp];
        refine' (div_le_div_right _).2 hx;
        erw [(rfl : @Zero.zero Real (MulZeroClassₓ.toHasZero Real) = 0)]
        exact hy }
      { erw [(rfl : @Zero.zero Real (MulZeroClassₓ.toHasZero Real) = 0)]
        apply le_of_ltₓ;
        exact hy } }
  | inr hyzx => {
      right 
      rcases hyzx with ⟨hy, h0z, hx0⟩
      apply And.intro hy;
      exact ⟨le_transₓ h0z hz, le_transₓ hx hx0⟩ }

declare_atom Vec.expCone [cone] (n : Nat)& (x : (Finₓ n) → ℝ)- (z : (Finₓ n) → ℝ)+ : Vec.expCone x 1 z :=
optimality by
  intros x' z' hx hz hexp i
  unfold Vec.expCone at *
  apply (exp_iff_expCone _ _).1
  have hexpleexp := exp_le_exp.2 (hx i)
  exact (hexpleexp.trans ((exp_iff_expCone _ _).2 (hexp i))).trans (hz i)

declare_atom posOrthCone [cone] (n : Nat)& (x : ℝ)+ : posOrthCone x :=
optimality by
  intros x' hx hx0
  exact hx0.trans hx

declare_atom Vec.posOrthCone [cone] 
  (n : Nat)& (x : (Fin n) → ℝ)+ : Vec.posOrthCone x :=
optimality by
  intros x' hx hx0 i
  exact (hx0 i).trans (hx i)

declare_atom Matrix.posOrthCone [cone] 
  (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)+ :
  Real.Matrix.posOrthCone M :=
optimality by
  intros x' hx hx0 i j
  exact (hx0 i j).trans (hx i j)

declare_atom rotatedSoCone [cone] (n : Nat)& (v : ℝ)+ (w : ℝ)+ (x : (Fin n) → ℝ)? :
  rotatedSoCone v w x :=
optimality by
  intros v' w' hv hw h
  unfold rotatedSoCone at *
  apply And.intro
  · apply h.1.trans
    apply mul_le_mul_of_nonneg_right
    apply mul_le_mul_of_le_of_le hv hw h.2.1 (h.2.2.trans hw)
    norm_num
  · exact ⟨h.2.1.trans hv, h.2.2.trans hw⟩

declare_atom Vec.rotatedSoCone [cone] (m : Nat)& (n : Nat)& (v : (Fin n) → ℝ)+ (w : (Fin n) → ℝ)+ (x : (Fin n) → (Fin m) → ℝ)? :
  Vec.rotatedSoCone v w x :=
optimality by
  unfold Vec.rotatedSoCone
  intros v' w' hv hw h i
  apply rotatedSoCone.optimality _ _ _ _ _ _ (hv i) (hw i) (h i)
  
declare_atom Matrix.PSDCone [cone] (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)? : 
  Matrix.PSDCone A :=
optimality fun h => h

end Cones

-- Affine operations.
section RealAffine

open Real

declare_atom add [affine] (x : ℝ)+ (y : ℝ)+ : x + y :=
bconditions
homogenity by
  simp [mul_add]
additivity by
  simp only [add_zero, add_assoc, add_comm]
  rw [add_comm x' y', ←add_assoc y y' x', add_comm _ x']
optimality fun _ _ => add_le_add

declare_atom neg [affine] (x : ℝ)- : - x :=
bconditions
homogenity by
  simp [neg_zero, add_zero]
additivity by
  rw [neg_add]
  simp
optimality by
  intros x' hx
  apply neg_le_neg hx

declare_atom maximizeNeg [affine] (x : ℝ)- : maximizeNeg x :=
bconditions
homogenity by
  simp [maximizeNeg, neg_zero, add_zero]
additivity by
  unfold maximizeNeg
  rw [neg_add]
  simp
optimality by
  intros x' hx
  apply neg_le_neg hx

declare_atom sub [affine] (x : ℝ)+ (y : ℝ)- : x - y :=
bconditions
homogenity by
  change _ * _ + _ = _ * _ - _ * _ + _ * _
  ring
additivity by
  ring
optimality by
  intros x' y' hx hy
  apply sub_le_sub hx hy

declare_atom mul1 [affine] (x : ℝ)& (y : ℝ)+ : x * y :=
bconditions (hx : 0 ≤ x)
homogenity by
  change _ * _ + _ = _ * (_ * _) + _ * _
  ring
additivity by
  ring
optimality by
  intros y' hy
  apply mul_le_mul_of_nonneg_left hy hx

declare_atom mul2 [affine] (x : ℝ)+ (y : ℝ)& : x * y :=
bconditions (hy : 0 ≤ y)
homogenity by
  change _ * _ + _ = (_ * _) * _ + _ * _
  ring
additivity by
  ring
optimality by
  intros y' hx
  apply mul_le_mul_of_nonneg_right hx hy

declare_atom mul3 [affine] (x : ℝ)& (y : ℝ)- : x * y :=
bconditions (hx : x ≤ 0)
homogenity by
  simp
  ring
additivity by
  ring
optimality by
  intros y' hy
  apply mul_le_mul_of_nonpos_left hy hx

declare_atom mul4 [affine] (x : ℝ)- (y : ℝ)& : x * y :=
bconditions (hy : y ≤ 0)
homogenity by
  change _ * _ + _ = (_ * _) * _ + _ * _
  ring
additivity by
  ring
optimality by
  intros y' hx
  apply mul_le_mul_of_nonpos_right hx hy

end RealAffine

-- Affine operations on vectors.
section VecAffine

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

declare_atom Vec.add [affine] (m : Nat)&  (x : Fin m → ℝ)+ (y : Fin m → ℝ)+ : x + y :=
bconditions
homogenity by
  simp [smul_add]
additivity by
  ring
optimality by
  intros x' y' hx hy i
  apply add_le_add (hx i) (hy i)

declare_atom Vec.sub [affine] (m : Nat)& (x : Fin m → ℝ)+ (y : Fin m → ℝ)- : x - y :=
bconditions
homogenity by
  simp [smul_sub]
additivity by
  ring
optimality by
  intros x' y' hx hy i
  exact sub_le_sub (hx i) (hy i)

declare_atom Vec.sum [affine] (m : Nat)& (x : Fin m → ℝ)+ : Vec.sum x :=
bconditions
homogenity by
  unfold Vec.sum
  simp only [Pi.zero_apply]
  rw [Finset.smul_sum, Finset.sum_const_zero, add_zero, smul_zero, add_zero]
  rfl
additivity by
  unfold Vec.sum
  simp only [Pi.zero_apply, Pi.add_apply]
  rw [Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
optimality by
  intro x' hx
  apply Finset.sum_le_sum
  intros _ _
  apply hx

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

declare_atom Vec.dotProduct1 [affine] (m : Nat)& (x : Fin m → ℝ)& (y : Fin m → ℝ)? : Matrix.dotProduct x y := 
bconditions
homogenity by
  rw [Matrix.dotProduct_zero, smul_zero, add_zero, add_zero, 
      Matrix.dotProduct_smul']
additivity by
  rw [Matrix.dotProduct_zero, add_zero, Matrix.dotProduct_add]
optimality le_refl _

declare_atom Vec.dotProduct2 [affine] (m : Nat)& (x : Fin m → ℝ)? (y : Fin m → ℝ)& : Matrix.dotProduct x y := 
bconditions
homogenity by
  rw [Matrix.zero_dotProduct, smul_zero, add_zero, add_zero,
      Matrix.smul_dotProduct']
additivity by
  rw [Matrix.zero_dotProduct, add_zero, Matrix.add_dotProduct]
optimality le_refl _

declare_atom smul [affine] (n : ℕ)& (y : ℝ)+ : n • y :=
bconditions
homogenity by
  rw [smul_zero, add_zero, smul_zero, add_zero, smul_comm]
additivity by
  rw [smul_zero, add_zero, smul_add]
optimality by
  intros y' hy
  apply smul_le_smul_of_nonneg hy (Nat.zero_le _)

end VecAffine

-- Affine operations on matrices.
section MatrixAffine 

open Matrix

declare_atom Matrix.vec_cons [affine] (n : Nat)& (x : ℝ)+ (y : (Fin n) → ℝ)+ : 
  Matrix.vecCons x y :=
bconditions
homogenity by
  simp only [Matrix.vecCons_zero_zero, smul_zero, add_zero, Matrix.smul_vecCons]
additivity by
  simp only [Matrix.add_vecCons, add_zero]
optimality by
  intros x' y' hx hy i
  refine' Fin.cases _ _ i <;> simp [Matrix.vecCons]
  . exact hx
  . exact hy

declare_atom Matrix.sum [affine] (m : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)+ : Matrix.sum X :=
bconditions
homogenity by
  simp only [Matrix.sum_zero]
  rw [smul_zero, add_zero, add_zero, Matrix.smul_sum]
additivity by
  simp only [Matrix.sum_zero]
  rw [add_zero, Matrix.sum_add]
optimality by
  intros X' hX
  apply Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  apply hX

declare_atom Matrix.nth [affine] (m : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)? (i : Fin m)& : X i :=
bconditions
homogenity by
  rw [Pi.zero_apply, add_zero, smul_zero, add_zero]
  rfl
additivity by
  rw [Pi.zero_apply, add_zero]
  rfl
optimality le_refl _

declare_atom Matrix.nth2 [affine] (m : Nat)& (X : Matrix.{0,0,0} (Fin m) (Fin m) ℝ)? (i : Fin m)& (j : Fin m)& : X i j :=
bconditions
homogenity by
  rw [Pi.zero_apply, Pi.zero_apply, smul_zero]
  rfl
additivity by
  rw [Pi.zero_apply, Pi.zero_apply, add_zero]
  rfl
optimality le_refl _

-- TODO: make argument increasing, without breaking det-log-atom
declare_atom Matrix.diag [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)? : A.diag :=
bconditions
homogenity by
  rw [Matrix.diag_zero, add_zero, smul_zero, add_zero]
  rfl
additivity by
  rw [Matrix.diag_zero, add_zero]
  rfl
optimality le_refl _

declare_atom Matrix.diagonal [affine] (n : ℕ)& (d : Fin n → ℝ)+ : Matrix.diagonal d :=
bconditions
homogenity by
  rw [Matrix.diagonal_zero', add_zero, smul_zero, add_zero, 
      Matrix.diagonal_smul']
additivity by
  rw [Matrix.diagonal_add', Matrix.diagonal_zero', add_zero]
optimality by
  intros d' hd i j
  by_cases h : i = j <;> simp [Matrix.diagonal, h, hd j]

declare_atom Matrix.trace [affine] (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)+ : Matrix.trace A:=
bconditions
homogenity by 
  rw [Matrix.trace_zero', add_zero, smul_zero, add_zero, Matrix.trace_smul']
additivity by
  rw [Matrix.trace_add', Matrix.trace_zero', add_zero]
optimality by
  intros A' hA
  apply Finset.sum_le_sum
  intros i _
  exact hA i i

declare_atom Matrix.toUpperTri [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ : 
  Matrix.toUpperTri A :=
bconditions
homogenity by
  rw [Matrix.toUpperTri_zero, add_zero, smul_zero, add_zero, 
      Matrix.toUpperTri_smul]
additivity by
  rw [Matrix.toUpperTri_zero, add_zero, Matrix.toUpperTri_add]
optimality by
  intros A' hA i j
  by_cases h : i ≤ j <;> simp [Matrix.toUpperTri, h] ; exact hA i j

declare_atom Matrix.transpose [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ : 
  A.transpose :=
bconditions
homogenity by
  rw [Matrix.transpose_zero', smul_zero]
  rfl
additivity by
  rw [Matrix.transpose_zero', add_zero, Matrix.transpose_add']
optimality by
  intros _ hA i j
  exact hA j i

declare_atom Matrix.fromBlocks [affine] (n : ℕ)& 
  (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ 
  (B : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+
  (C : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ 
  (D : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)+ :
  Matrix.fromBlocks A B C D :=
bconditions
homogenity by
  rw [Matrix.fromBlocks_zero, smul_zero, add_zero, add_zero, 
      Matrix.fromBlocks_smul']
additivity by
  simp [Matrix.fromBlocks_add]
optimality by
  intros A' B' C' D' hA hB hC hD i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks] 
  . exact hA _ _
  . exact hB _ _
  . exact hC _ _
  . exact hD _ _

declare_atom Matrix.add [affine] (m : Type)& (n : Type)& (A : Matrix.{0,0,0} m n ℝ)+ (B : Matrix.{0,0,0} m n ℝ)+ : A + B :=
bconditions
homogenity by
  rw [add_zero, add_zero, smul_zero, add_zero, smul_add]
additivity by
  rw [add_zero, add_zero, add_assoc, add_comm B, add_assoc A', add_comm B']
  simp only [add_assoc]
optimality by
  intros A' B' hA hB i j
  apply add_le_add (hA i j) (hB i j)

declare_atom Matrix.sub [affine] (m : Type)& (n : Type)& 
  (A : Matrix.{0,0,0} m n ℝ)+ (B : Matrix.{0,0,0} m n ℝ)- : A - B :=
bconditions
homogenity by
  funext i j
  simp [mul_sub]
additivity by
  rw [sub_self, add_zero, sub_add_sub_comm]
optimality by
  intros A' B' hA hB i j
  exact sub_le_sub (hA i j) (hB i j)

-- TODO: Notation
declare_atom Matrix.mul1 [affine] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)& (B : Matrix.{0,0,0} m m ℝ)? : A * B :=
bconditions
homogenity by
  simp
additivity by 
  simp [Matrix.mul_add]
optimality le_refl _

-- TODO: Notation
declare_atom Matrix.mul2 [affine] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)? (B : Matrix.{0,0,0} m m ℝ)& : A * B :=
bconditions
homogenity by
  simp
additivity by 
  simp [Matrix.add_mul]
optimality le_refl _

declare_atom Matrix.mulVec [affine] (n : ℕ)& (m : ℕ)& 
  (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)& (v : Fin n → ℝ)? : Matrix.mulVec M v :=
bconditions
homogenity by
  rw [Matrix.mulVec_zero', smul_zero, add_zero, add_zero, Matrix.mulVec_smul']
additivity by
  simp [Matrix.mulVec_add', Matrix.mulVec_zero', add_zero]
optimality le_refl _

end MatrixAffine 

-- Non-affine atoms on real variables.
section Real

open Real

declare_atom le [concave] (x : ℝ)- (y : ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.posOrthCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by 
  simp [Real.posOrthCone]
feasibility
optimality by
  intros x' y' hx hy h
  simp [Real.posOrthCone] at h 
  exact (hx.trans h).trans hy
vconditionElimination

declare_atom eq [concave] (x : ℝ)? (y : ℝ)? : x = y := 
vconditions
implementationVars
implementationObjective Real.zeroCone (y - x)
implementationConstraints
solution
solutionEqualsAtom by 
  simp [Real.zeroCone, sub_eq_iff_eq_add, zero_add]
  exact Iff.intro Eq.symm Eq.symm;
feasibility
optimality by 
  simp [Real.zeroCone, sub_eq_iff_eq_add, zero_add]
  exact Eq.symm
vconditionElimination

declare_atom sq [convex] (x : ℝ)? : x ^ 2 := 
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : rotatedSoCone t (1/2) ![x])
solution
  (t := x ^ 2)
solutionEqualsAtom rfl
feasibility
  (c1 : by 
    simp [rotatedSoCone]
    exact ⟨sq_nonneg x, zero_le_two⟩)
optimality by
  have h := c1.1
  simp at h ⊢
  exact h
vconditionElimination 

declare_atom exp [convex] (x : ℝ)+ : Real.exp x :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone x 1 t)
solution (t := exp x)
solutionEqualsAtom by
  rfl;
feasibility 
  (c_exp : by 
    simp [expCone])
optimality by
  intros x' hx
  rw [←exp_iff_expCone] at c_exp
  have hexpleexp := exp_le_exp.2 hx
  exact hexpleexp.trans c_exp
vconditionElimination

declare_atom sqrt [concave] (x : ℝ)+ : Real.sqrt x := 
vconditions (cond : 0 ≤ x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints 
  (c1 : rotatedSoCone x (1/2) ![t])
solution (t := Real.sqrt x)
solutionEqualsAtom by
  rfl;
feasibility 
  (c1 : by
    simp [rotatedSoCone]
    refine ⟨?_, cond, zero_le_two⟩
    rw [sq_sqrt cond])
optimality by
  intros y hy 
  simp [rotatedSoCone] at c1
  have h := c1.1
  exact Real.le_sqrt_of_sq_le (le_trans h hy)
vconditionElimination (cond : fun _ hx => c1.2.1.trans hx)

declare_atom log [concave] (x : ℝ)+ : log x :=
vconditions (cond : 0 < x)
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone t 1 x)
solution (t := log x)
solutionEqualsAtom by 
  rfl;
feasibility (c_exp : by 
  simp [expCone]
  rw [Real.exp_log cond])
optimality by
  intros y hy
  simp [expCone] at c_exp 
  have hxpos := lt_of_lt_of_le (exp_pos t) c_exp
  have hypos := lt_of_lt_of_le hxpos hy
  have hexptley := le_trans c_exp hy
  exact (le_log_iff_exp_le hypos).2 hexptley
vconditionElimination 
  (cond : by
    intros y hy
    simp [expCone] at c_exp
    have hexppos := exp_pos t
    have hxpos := lt_of_lt_of_le hexppos c_exp
    exact lt_of_lt_of_le hxpos hy)

declare_atom abs [convex] (x : ℝ)? : abs x :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints
  (c_pos : posOrthCone (t - x))
  (c_neg : posOrthCone (t + x))
solution (t := abs x)
solutionEqualsAtom rfl
feasibility 
  (c_pos : by
    unfold posOrthCone
    rw [sub_nonneg]
    exact le_abs_self x) 
  (c_neg : by
    unfold posOrthCone
    rw [←neg_le_iff_add_nonneg']
    exact neg_abs_le_self x)
optimality by
  apply abs_le.2
  rw [←sub_nonneg, sub_neg_eq_add, add_comm, ←sub_nonneg (b := x)]
  exact ⟨c_neg, c_pos⟩
vconditionElimination

end Real

-- Non-affine atoms on vectors.
section Vec

open Vec

declare_atom Vec.le [concave] (n : Nat)& (x : (Fin n) → ℝ)- (y : (Fin n) → ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.Vec.posOrthCone (y - x : (Fin n) → ℝ)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Vec.posOrthCone
  unfold Real.posOrthCone
  rw [← iff_iff_eq]
  constructor
  · intros h i
    rw [← le.solEqAtom]
    apply h
  · intros h i
    erw [le.solEqAtom]
    apply h
feasibility
optimality by
  intros x' y' hx hy h i
  apply le.optimality _ _ _ _ (hx i) (hy i) (h i)
vconditionElimination

declare_atom Vec.exp [convex] (n : Nat)& (x : (Fin n) → ℝ)+ : exp x :=
vconditions
implementationVars (t : Fin n → ℝ)
implementationObjective t
implementationConstraints (c_exp : Real.Vec.expCone x 1 t)
solution (t := exp x)
solutionEqualsAtom 
  rfl
feasibility 
  (c_exp: by
    intros _ _
    apply exp.feasibility0)
optimality by
  intros x' hx i
  apply exp.optimality _ _ (c_exp i) _ (hx i)
vconditionElimination

declare_atom Vec.log [concave] (n : Nat)& (x : (Fin n) → ℝ)+ : log x :=
vconditions (cond : ∀ i, 0 < x i)
implementationVars (t : (Fin n) → ℝ)
implementationObjective t
implementationConstraints (c_exp : Real.Vec.expCone t 1 x)
solution (t := log x)
solutionEqualsAtom rfl
feasibility 
  (c_exp: by
    intros _ i
    apply log.feasibility0
    apply cond)
optimality by
  intros x' hx i
  apply log.optimality _ _ (c_exp i) _ (hx i)
vconditionElimination (cond : by
  intros x' hx i
  apply log.vcondElim0 _ _ (c_exp i) _ (hx i))

declare_atom Vec.abs [convex] (n : Nat)& (x : (Fin n) → ℝ)? : abs x :=
vconditions
implementationVars (t : (Fin n) → ℝ)
implementationObjective t
implementationConstraints
  (c_pos : Real.Vec.posOrthCone (t - x : (Fin n) → ℝ))
  (c_neg : Real.Vec.posOrthCone (t + x : (Fin n) → ℝ))
solution (t := abs x)
solutionEqualsAtom rfl
feasibility
  (c_pos : by
    intros _ _
    apply abs.feasibility0)
  (c_neg : by
    intros _ _
    apply abs.feasibility1)
optimality by
  intros i
  apply abs.optimality _ _ (c_pos i) (c_neg i)
vconditionElimination

end Vec

-- Non-affine atoms on matrices.
namespace Matrix

declare_atom Matrix.PosSemidef [concave] 
  (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)? 
  : Matrix.PosSemidef A :=
vconditions
implementationVars
implementationObjective Real.Matrix.PSDCone A
implementationConstraints
solution
solutionEqualsAtom by simp [Real.Matrix.PSDCone]
feasibility
optimality by simp [Real.Matrix.PSDCone]
vconditionElimination

declare_atom Matrix.logDet [concave] (n : ℕ)& (A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)? : Real.log A.det :=
vconditions (hA : A.PosDef)
implementationVars (t : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ)
-- The lower left values of `Y` are unused. CVXPy uses a vector `z` instead of a matrix `Y`.
implementationObjective Vec.sum t
implementationConstraints 
  (c_exp : Real.Vec.expCone t 1 Y.diag)
  (c_posdef : Matrix.PosSemidef $
    let Z := Y.toUpperTri;
    let D := Matrix.diagonal Y.diag
    let X := Matrix.fromBlocks D            Z 
                               Z.transpose  A;
    X)
solution 
  (t := 
    have : Decidable (A.PosDef) := Classical.dec _ 
    if h : A.PosDef then Vec.log (LDL.diagEntries h) else 0) 
  (Y :=
    have : Decidable (A.PosDef) := Classical.dec _ 
    if h : A.PosDef then (LDL.diag h) * (LDL.lower h).transpose else 0) 
solutionEqualsAtom by
  simp only [dif_pos hA, Vec.sum, Vec.log]
  rw [Matrix.LogDetAtom.solution_eq_atom hA]
  congr
feasibility 
  (c_exp : by
    simp only [Real.Vec.expCone, dif_pos hA]
    intro i
    show Real.expCone ((Real.log (LDL.diagEntries hA i))) 1
      (Matrix.diag ((LDL.diag hA) * (LDL.lower hA).transpose) i)
    rw [← Real.exp_iff_expCone, Real.exp_log]
    exact Matrix.LogDetAtom.feasibility_exp hA i
    exact Matrix.LDL.diagEntries_pos hA i)
  (c_posdef : by
    simp only [dif_pos hA]
    convert Matrix.LogDetAtom.feasibility_PosDef' hA rfl rfl rfl)
optimality by
  have ht : ∀ (i : Fin n), Real.exp (t i) ≤ Matrix.diag Y i := by 
    intro i
    rw [Real.exp_iff_expCone]
    apply c_exp
  -- TODO(RFM): Why does exact fail here?
  have h := @Matrix.LogDetAtom.optimality (Fin n) _ _ A t Y (Matrix.toUpperTri Y) 
    (Matrix.diagonal Y.diag) ht (by convert rfl) (by convert rfl) c_posdef
  refine' Eq.mp _ h
  congr
vconditionElimination 
  (hA : by
    have ht : ∀ (i : Fin n), Real.exp (t i) ≤ Matrix.diag Y i := by 
      intro i
      rw [Real.exp_iff_expCone]
      apply c_exp
    exact @Matrix.LogDetAtom.cond_elim (Fin n) _ _ A t Y (Matrix.toUpperTri Y) 
      (Matrix.diagonal (Matrix.diag Y)) ht (by convert rfl) (by convert rfl) c_posdef)

declare_atom Matrix.abs [convex] 
  (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Fin m) (Fin n) ℝ)? 
  : M.abs :=
vconditions
implementationVars (T : Matrix (Fin m) (Fin n) ℝ)
implementationObjective T
implementationConstraints
  (c_pos : Real.Matrix.posOrthCone (T - M : Matrix (Fin m) (Fin n) ℝ))
  (c_neg : Real.Matrix.posOrthCone (T + M : Matrix (Fin m) (Fin n) ℝ))
solution (T := M.abs)
solutionEqualsAtom rfl
feasibility
  (c_pos : by 
    intros _ _ _
    apply abs.feasibility0)
  (c_neg :  by 
    intros _ _ _
    apply abs.feasibility1)
optimality by
  intros i j
  apply abs.optimality _ _ (c_pos i j) (c_neg i j)
vconditionElimination

end Matrix
