import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Cones
import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Missing.Matrix
import CvxLean.Syntax.Minimization
import Optbin.All
import Mathbin.Algebra.Order.MonoidLemmasZeroLt
import Mathbin.Algebra.Order.Group

namespace CvxLean

-- Constraints in conic form.
section Cones

open Real

-- Optimality for using a variable in the second argument
-- will be hard to prove optimality for.
declare_atom expCone [cone] (x : ℝ)- (z : ℝ)+ : expCone x 1 z :=
optimality by
  intros x' z' hx hz hexp
  rw [←exp_iff_expCone] at *
  exact ((exp_le_exp.2 hx).transₓ hexp).transₓ hz

declare_atom Vec.expCone [cone] (n : Nat)& (x : (Finₓ n) → ℝ)- (z : (Finₓ n) → ℝ)+ : Vec.expCone x 1 z :=
optimality by
  intros x' z' hx hz hexp i
  unfold Vec.expCone at *
  apply (exp_iff_expCone _ _).1
  exact ((exp_le_exp.2 (hx i)).transₓ ((exp_iff_expCone _ _).2 (hexp i))).transₓ (hz i)

declare_atom posOrthCone [cone] (n : Nat)& (x : ℝ)+ : posOrthCone x :=
optimality by
  intros x' hx hx0
  exact hx0.transₓ hx

declare_atom Vec.posOrthCone [cone] (n : Nat)& (x : (Finₓ n) → ℝ)+ : Vec.posOrthCone x :=
optimality by
  intros x' hx hx0 i
  exact (hx0 i).transₓ (hx i)

declare_atom Matrix.posOrthCone [cone] (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Finₓ m) (Finₓ n) ℝ)+ :
  Real.Matrix.posOrthCone M :=
optimality by
  intros x' hx hx0 i j
  exact (hx0 i j).transₓ (hx i j)

declare_atom rotatedSoCone [cone] (n : Nat)& (v : ℝ)+ (w : ℝ)+ (x : (Finₓ n) → ℝ)? :
  rotatedSoCone v w x :=
optimality by
  intros v' w' hv hw h
  unfold rotatedSoCone at *
  apply And.intro
  · apply h.1.transₓ
    apply ZeroLt.mul_le_mul_of_nonneg_right
    apply ZeroLt.mul_le_mul_of_le_of_le hv hw h.2.1 (h.2.2.transₓ hw)
    have : @Zero.zero Real (MulZeroClassₓ.toHasZero Real) = 0 := by
      rfl
    rw [this]
    simp only [(@Nat.cast_zero ℝ _).symm, (@Nat.cast_one ℝ _).symm]
    apply Nat.cast_le.2
    norm_num
  · exact ⟨h.2.1.transₓ hv, h.2.2.transₓ hw⟩

declare_atom Vec.rotatedSoCone [cone] (m : Nat)& (n : Nat)& (v : (Finₓ n) → ℝ)+ (w : (Finₓ n) → ℝ)+ (x : (Finₓ n) → (Finₓ m) → ℝ)? :
  Vec.rotatedSoCone v w x :=
optimality by
  unfold Vec.rotatedSoCone
  intros v' w' hv hw h i
  apply rotatedSoCone.optimality _ _ _ _ _ _ (hv i) (hw i) (h i)
  
declare_atom Matrix.PSDCone [cone] (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)? : 
  Matrix.PSDCone A :=
optimality fun h => h

end Cones

-- NOTE: Workaround for nonterminating simp.
attribute [-simp] Quot.lift_on_mk Quot.lift_on₂_mk Quot.lift₂_mk

-- Affine operations.
section RealAffine

open Real

declare_atom add [affine] (x : ℝ)+ (y : ℝ)+ : x + y :=
bconditions
homogenity by
  change _ = _ + _ + HasSmul.smul κ (Zero.zero + Zero.zero)
  rw [smul_add, smul_add, smul_zero]
  rfl
additivity by
  simp only [add_zero, add_assoc, add_commₓ]
  rw [add_commₓ x' y', ←add_assocₓ y y' x', add_commₓ _ x']
optimality fun _ _ => add_le_add

declare_atom neg [affine] (x : ℝ)- : - x :=
bconditions
homogenity by
  change HasSmul.smul κ (-x) + -Zero.zero = 
    -HasSmul.smul κ x + HasSmul.smul κ (-Zero.zero)
  simp
  rw [smul_zero, smul_neg, add_zeroₓ]
  rfl
additivity by
  rw [neg_add]
  simp
  rfl
optimality by
  intros x' hx
  apply neg_le_neg hx

declare_atom maximizeNeg [affine] (x : ℝ)- : maximizeNeg x :=
bconditions
homogenity by
  change HasSmul.smul κ (-x) + -Zero.zero = 
    -HasSmul.smul κ x + HasSmul.smul κ (-Zero.zero)
  simp
  rw [smul_zero, smul_neg, add_zeroₓ]
  rfl
additivity by
  unfold maximizeNeg
  rw [neg_add]
  simp
  rfl
optimality by
  intros x' hx
  apply neg_le_neg hx

declare_atom sub [affine] (x : ℝ)+ (y : ℝ)- : x - y :=
bconditions
homogenity by
  rw [smul_sub, sub_self, smul_zero]
  rfl
additivity by
  rw [sub_add_comm, add_commₓ, add_sub, add_sub_assoc, sub_sub, add_commₓ y' y, 
    add_sub, sub_self, add_zeroₓ]
optimality by
  intros x' y' hx hy
  apply @sub_le_sub Real _ _ 
    (@OrderedAddCommGroup.to_covariant_class_left_le Real Real.orderedAddCommGroup) 
  exact hx
  exact hy

declare_atom mul1 [affine] (x : ℝ)& (y : ℝ)+ : x * y :=
bconditions (hx : 0 ≤ x)
homogenity by
  change HasSmul.smul κ (x * y) + x * Zero.zero
    = x * HasSmul.smul κ y + HasSmul.smul κ (x * Zero.zero)
  rw [_root_.mul_zero, smul_zero, add_zeroₓ, add_zeroₓ, mul_smul_comm]
additivity by
  change x * y + x * y' = x * (y + y') + x * Zero.zero
  rw [mul_addₓ, _root_.mul_zero, add_zeroₓ]
optimality by
  intros y' hy
  apply ZeroLt.mul_le_mul_of_nonneg_left hy hx

declare_atom mul2 [affine] (x : ℝ)+ (y : ℝ)& : x * y :=
bconditions (hy : 0 ≤ y)
homogenity by
  change HasSmul.smul κ (x * y) + Zero.zero * y 
    = (HasSmul.smul κ x) * y + HasSmul.smul κ (Zero.zero * y)
  rw [_root_.zero_mul, smul_zero, add_zeroₓ, add_zeroₓ,
    _root_.mul_comm, _root_.mul_comm _ y, mul_smul_comm]
additivity by
  change x * y + x' * y = (x + x') * y + Zero.zero * y
  rw [add_mulₓ, _root_.zero_mul, add_zeroₓ]
optimality by
  intros y' hx
  apply ZeroLt.mul_le_mul_of_nonneg_right hx hy

end RealAffine

-- Affine operations on vectors.
section VecAffine

declare_atom Vec.nth [affine] (m : Nat)&  (x : Finₓ m → ℝ)? (i : Finₓ m)& : x i :=
bconditions
homogenity by
  change HasSmul.smul κ (x i) + Zero.zero
    = HasSmul.smul κ x i + HasSmul.smul κ Zero.zero
  rw [smul_zero, add_zeroₓ, add_zeroₓ]
  rfl
additivity by
  change x i + x' i = x i + x' i + Zero.zero
  rw [add_zeroₓ]
optimality le_reflₓ _

declare_atom Vec.add [affine] (m : Nat)&  (x : Finₓ m → ℝ)+ (y : Finₓ m → ℝ)+ : x + y :=
bconditions
homogenity by
  change HasSmul.smul κ (x + y) + (Zero.zero + Zero.zero) 
    = HasSmul.smul κ x + HasSmul.smul κ y + HasSmul.smul κ (Zero.zero + Zero.zero)
  rw [add_zeroₓ, add_zeroₓ, smul_zero, add_zeroₓ, smul_add]
  rfl
additivity by
  change x + y + (x' + y') = x + x' + (y + y') + (Zero.zero + Zero.zero)
  rw [add_zeroₓ, add_zeroₓ, add_assocₓ, add_commₓ x' y', ←add_assocₓ y, add_commₓ _ x']
  simp [add_assocₓ]
optimality by
  intros x' y' hx hy i
  apply add_le_add (hx i) (hy i)

declare_atom Vec.sub [affine] (m : Nat)&  (x : Finₓ m → ℝ)+ (y : Finₓ m → ℝ)- : x - y :=
bconditions
homogenity by
  rw [sub_self, smul_sub, smul_zero]
  rfl
additivity by
  rw [sub_add_sub_comm, sub_self, add_zeroₓ]
optimality by
  intros x' y' hx hy i
  apply @sub_le_sub Real _ _ 
    (@OrderedAddCommGroup.to_covariant_class_left_le Real Real.orderedAddCommGroup)
  exact (hx i)
  exact (hy i)

declare_atom Vec.sum [affine] (m : Nat)& (x : Finₓ m → ℝ)+ : Vec.sum x :=
bconditions
homogenity by
  change HasSmul.smul κ (Vec.sum x) + (∑ i, Zero.zero)
    = Vec.sum (HasSmul.smul κ x) + HasSmul.smul κ (∑ i, Zero.zero)
  unfold Vec.sum
  rw [Finset.smul_sum, Finset.sum_const_zero, add_zeroₓ, smul_zero, add_zeroₓ]
  rfl
additivity by
  change (∑ i, x i) + (∑ i, x' i) = (∑ i, x i + x' i) + ∑ i, Zero.zero
  rw [Finset.sum_const_zero, add_zeroₓ, Finset.sum_add_distrib]
optimality by
  intro x' hx
  apply Finset.sum_le_sum
  intros
  apply hx

declare_atom div [affine] (x : ℝ)+ (y : ℝ)& : x / y :=
bconditions (hy : (0 : ℝ) ≤ y)
homogenity by
  change κ * (x / y) + Zero.zero / y 
    = κ * x / y + κ * (Zero.zero / y)
  rw [zero_div, add_zeroₓ, _root_.mul_zero, add_zeroₓ, mul_div]
additivity by
  change x / y + x' / y = (x + x') / y + Zero.zero / y
  rw [zero_div, add_zeroₓ, add_div]
optimality by
  intros x' hx
  by_cases h : Zero.zero = y
  · rw [←h, div_zero, div_zero]
    exact le_reflₓ _
  · rw [div_le_div_right]
    apply hx
    apply lt_of_le_of_neₓ hy h

declare_atom Vec.dotProduct1 [affine] (m : Nat)& (x : Finₓ m → ℝ)& (y : Finₓ m → ℝ)? : Matrix.dotProduct x y := 
bconditions
homogenity by
  change κ * (Matrix.dotProduct x y) + Matrix.dotProduct x Zero.zero =
    Matrix.dotProduct x (HasSmul.smul κ y) + κ * (Matrix.dotProduct x Zero.zero)
  rw [Matrix.dot_product_zero, add_zeroₓ, _root_.mul_zero, add_zeroₓ,
    Matrix.dot_product_smul]
  rfl
additivity by
  change Matrix.dotProduct x y + Matrix.dotProduct x y'
    = Matrix.dotProduct x (y + y') + Matrix.dotProduct x Zero.zero
  rw [Matrix.dot_product_zero, add_zeroₓ, Matrix.dot_product_add]
optimality le_reflₓ _

declare_atom Vec.dotProduct2 [affine] (m : Nat)& (x : Finₓ m → ℝ)? (y : Finₓ m → ℝ)& : Matrix.dotProduct x y := 
bconditions
homogenity by
  change κ * (Matrix.dotProduct x y) + Matrix.dotProduct Zero.zero y =
    Matrix.dotProduct (HasSmul.smul κ x) y + κ * (Matrix.dotProduct Zero.zero y)
  rw [Matrix.zero_dot_product, add_zeroₓ, _root_.mul_zero, add_zeroₓ,
    Matrix.dot_product_comm (HasSmul.smul κ x), Matrix.dot_product_smul, Matrix.dot_product_comm]
  rfl
additivity by
  change Matrix.dotProduct x y + Matrix.dotProduct x' y
    = Matrix.dotProduct (x + x' : Finₓ m → Real) y + Matrix.dotProduct Zero.zero y
  rw [Matrix.zero_dot_product, add_zeroₓ, Matrix.add_dot_product]
optimality le_reflₓ _

declare_atom smul [affine] (n : ℕ)& (y : ℝ)+ : @HasSmul.smul ℕ Real AddMonoidₓ.hasSmulNat n y :=
bconditions
homogenity by
  change HasSmul.smul κ (HasSmul.smul n y) + HasSmul.smul n Zero.zero =
    HasSmul.smul n (HasSmul.smul κ y) + HasSmul.smul κ (HasSmul.smul n Zero.zero)
  rw [smul_zero, add_zeroₓ, smul_zero, smul_zero, add_zeroₓ, smul_comm]
additivity by
  change HasSmul.smul n y + HasSmul.smul n y'
    = HasSmul.smul n (y + y') + HasSmul.smul n Zero.zero
  rw [smul_zero, add_zeroₓ, smul_add]
  rfl
optimality by
  intros y' hy
  apply smul_le_smul_of_nonneg hy (Nat.zero_leₓ _)

end VecAffine

-- Affine operations on matrices.
section MatrixAffine 

declare_atom Matrix.vec_cons [affine] (n : Nat)& (x : ℝ)+ (y : (Finₓ n) → ℝ)+ : 
  Matrix.vecCons x y :=
bconditions
homogenity by
  change HasSmul.smul κ (Matrix.vecCons x y) + Matrix.vecCons (Zero.zero : ℝ) (Zero.zero : (Finₓ n) → ℝ) =
    Matrix.vecCons (κ * x) (HasSmul.smul κ y) + HasSmul.smul κ (Matrix.vecCons (Zero.zero : ℝ) (Zero.zero : (Finₓ n) → ℝ))
  ext ⟨i, hi⟩
  cases i
  · simp [HasSmul.smul, Matrix.Computable.Pi.hasSmul', Matrix.Computable.Mul.toHasSmul']
  · simp [HasSmul.smul, Matrix.Computable.Pi.hasSmul', Matrix.Computable.Mul.toHasSmul']
additivity by
  change Matrix.vecCons x y + Matrix.vecCons x' y'
    = Matrix.vecCons (x + x' : ℝ) (y + y' : (Finₓ n) → ℝ)
      + Matrix.vecCons (Zero.zero : ℝ) (Zero.zero : (Finₓ n) → ℝ)
  ext ⟨i, hi⟩
  cases i
  · simp
  · simp
optimality by
  intros x' y' hx hy i
  cases i with
  | mk i hi =>
    cases i with
    | zero => simp [hx]
    | succ i => simp [hy ⟨i, Nat.succ_lt_succ_iff.1 hi⟩]

declare_atom Matrix.sum [affine] (m : Nat)& (X : Matrix.{0,0,0} (Finₓ m) (Finₓ m) ℝ)+ : Matrix.sum X :=
bconditions
homogenity by
  change κ * (∑ i, ∑ j, X i j) + (∑ i, ∑ j, Zero.zero)
    = (∑ i, ∑ j, κ * X i j) + κ * (∑ i, ∑ j, Zero.zero)
  rw [Finset.sum_const_zero, Finset.sum_const_zero, _root_.mul_zero, add_zeroₓ, add_zeroₓ]
  simp only [Finset.mul_sum]
additivity by
  change (∑ i, ∑ j, X i j) + (∑ i, ∑ j, X' i j) 
    = (∑ i, ∑ j, X i j + X' i j) + ∑ i, ∑ j, Zero.zero
  rw [Finset.sum_const_zero, Finset.sum_const_zero, add_zeroₓ]
  simp only [Finset.sum_add_distrib]
optimality by
  intros X' hX
  apply Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  apply hX

declare_atom Matrix.nth [affine] (m : Nat)& (X : Matrix.{0,0,0} (Finₓ m) (Finₓ m) ℝ)? (i : Finₓ m)& : X i :=
bconditions
homogenity by
  change HasSmul.smul κ (X i) + Zero.zero = HasSmul.smul κ X i + HasSmul.smul κ Zero.zero
  rw [add_zeroₓ, smul_zero, add_zeroₓ]
  rfl
additivity by
  change X i + X' i = HAdd.hAdd X X' i + Zero.zero
  rw [add_zeroₓ]
  rfl
optimality le_reflₓ _

declare_atom Matrix.nth2 [affine] (m : Nat)& (X : Matrix.{0,0,0} (Finₓ m) (Finₓ m) ℝ)? (i : Finₓ m)& (j : Finₓ m)& : X i j :=
bconditions
homogenity by
  change _ + Zero.zero = _ + HasSmul.smul κ Zero.zero
  rw [smul_zero]
  rfl
additivity by
  change _ = _ + Zero.zero
  rw [add_zeroₓ]
  rfl
optimality le_reflₓ _
  
-- TODO: make argument increasing, without breaking det-log-atom
declare_atom Matrix.diag [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)? : A.diag :=
bconditions
homogenity by
  change _ + Zero.zero
    = _ + HasSmul.smul κ Zero.zero
  rw [add_zeroₓ, smul_zero, add_zeroₓ]
  rfl
additivity by
  change _  = _ + Zero.zero
  rw [add_zeroₓ]
  rfl
optimality le_reflₓ _

declare_atom Matrix.diagonal [affine] (n : ℕ)& (d : Finₓ n → ℝ)+ : Matrix.diagonal d :=
bconditions
homogenity by
  ext i j
  change
    κ * (Matrix.diagonalₓ d) i j + (Matrix.diagonal fun i => Zero.zero) i j =
    Matrix.diagonalₓ (HasSmul.smul κ d) i j + HasSmul.smul κ (Matrix.diagonal Zero.zero) i j
  by_cases h : i = j
  · simp [Matrix.diagonal, h]
    change κ * d j = HasSmul.smul κ d j + κ * Zero.zero
    rw [_root_.mul_zero, add_zeroₓ]
    rfl
  · simp [Matrix.diagonal, h]
    change Zero.zero = κ * Zero.zero
    rw [_root_.mul_zero]
additivity by
  change Matrix.diagonalₓ _ + Matrix.diagonalₓ _
    = _ + Matrix.diagonalₓ fun i => Zero.zero
  rw [Matrix.diagonal_add, Matrix.diagonal_zero, add_zeroₓ]
  rfl
optimality by
  intros d' hd i j
  by_cases h : i = j
  · simp [Matrix.diagonal, h, hd j]
  · simp [Matrix.diagonal, h, hd j]

declare_atom Matrix.diagonalₓ [affine] (n : ℕ)& (d : Finₓ n → ℝ)+ : Matrix.diagonalₓ d :=
bconditions
homogenity by
  ext i j
  change
    κ * (Matrix.diagonalₓ d) i j + (Matrix.diagonal fun i => Zero.zero) i j =
    Matrix.diagonalₓ (HasSmul.smul κ d) i j + HasSmul.smul κ (Matrix.diagonal Zero.zero) i j
  by_cases h : i = j
  · simp [Matrix.diagonal, h]
    change κ * d j = HasSmul.smul κ d j + κ * Zero.zero
    rw [_root_.mul_zero, add_zeroₓ]
    rfl
  · simp [Matrix.diagonal, h]
    change Zero.zero = κ * Zero.zero
    rw [_root_.mul_zero]
additivity by
  change _ = _ + Matrix.diagonalₓ fun i => Zero.zero
  rw [Matrix.diagonal_add, Matrix.diagonal_zero, add_zeroₓ]
  rfl
optimality by
  intros d' hd i j
  by_cases h : i = j
  · simp [Matrix.diagonal, h, hd j]
  · simp [Matrix.diagonal, h, hd j]

-- NOTE: Helper lemma needed due to mathport
lemma zero_eq_zero [Zero α] : (0 : α) = Zero.zero := rfl

declare_atom Matrix.trace [affine] (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)+ : Matrix.trace A:=
bconditions
homogenity by
  change HasSmul.smul κ (Matrix.trace A) + Matrix.trace Zero.zero
    = Matrix.trace (HasSmul.smul κ A) + HasSmul.smul κ (Matrix.trace Zero.zero)
  rw [← Matrix.trace_smul, ← Matrix.trace_smul, smul_zero]
  rfl
additivity by
  rw [zero_eq_zero, Matrix.trace_add, Matrix.trace_zero, add_zeroₓ]
optimality by
  intros A' hA
  apply Finset.sum_le_sum
  intros i _
  exact hA i i

declare_atom Matrix.toUpperTri [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+ : 
  A.toUpperTri :=
bconditions
homogenity by
  ext i j
  change κ * (Matrix.toUpperTri A) i j + (Matrix.toUpperTri 0) i j =
    (Matrix.toUpperTri (HasSmul.smul κ A)) i j + κ * (Matrix.toUpperTri Zero.zero) i j
  by_cases h : i ≤ j
  · unfold Matrix.toUpperTri
    simp [h]
    change κ * A i j + 0 = HasSmul.smul κ A i j + κ * Zero.zero
    rw [_root_.mul_zero]
    rfl
  · unfold Matrix.toUpperTri
    simp [h]
additivity by
  ext i j
  change (Matrix.toUpperTri A) i j+ (Matrix.toUpperTri A') i j =
    (Matrix.toUpperTri _) i j + (Matrix.toUpperTri Zero.zero) i j
  by_cases h : i ≤ j
  · unfold Matrix.toUpperTri
    simp [h]
    change A i j + A' i j = HAdd.hAdd A A' i j + Zero.zero
    rw [add_zeroₓ]
    rfl
  · unfold Matrix.toUpperTri
    simp [h]
optimality by
  intros A' hA
  ext i j
  by_cases h : i ≤ j
  · unfold Matrix.toUpperTri
    simp [h, hA i j]
  · unfold Matrix.toUpperTri
    simp [h]

declare_atom Matrix.transpose [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+ : 
  A.transpose :=
bconditions
homogenity by
  change _ = _ + HasSmul.smul _ (Matrix.transposeₓ Zero.zero)
  simp [zero_eq_zero, Matrix.transpose_zero]
  rw [smul_zero]
  rfl
additivity by
  change Matrix.transposeₓ _ + Matrix.transposeₓ _
    = Matrix.transposeₓ _ + Matrix.transposeₓ _
  simp
  rfl
optimality by
  intros _ hA
  ext i j
  exact hA j i

declare_atom Matrix.transposeₓ [affine] (n : ℕ)& (A : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+ : 
  A.transposeₓ :=
bconditions
homogenity by
  simp [zero_eq_zero, Matrix.transpose_zero]
  rw [smul_zero, add_zeroₓ]
  rfl
additivity by
  simp
  rfl
optimality by
  intros _ hA
  ext i j
  exact hA j i

@[simp] lemma Matrix.from_blocks_zero [Zero α]: 
  Matrix.fromBlocks (0 : Matrix n l α) (0 : Matrix n m α) (0 : Matrix o l α) (0 : Matrix o m α) = 0 := by
  ext i j
  cases i
  · cases j
    rfl
    rfl
  · cases j
    rfl
    rfl

declare_atom Matrix.fromBlocks [affine] (n : ℕ)& 
  (A : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+ (B : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+
  (C : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+ (D : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)+ :
  Matrix.fromBlocks A B C D :=
bconditions
homogenity by
  change _ = _ + HasSmul.smul κ _
  rw [Matrix.from_blocks_smul,  Matrix.from_blocks_zero, zero_eq_zero, smul_zero]
  rfl
additivity by
  simp [Matrix.from_blocks_add, zero_eq_zero]
optimality by
  intros A' B' C' D' hA hB hC hD i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  | inr i => 
    cases j with
    | inl j => exact hC i j
    | inr j => exact hD i j

declare_atom Matrix.add [affine] (m : Type)& (n : Type)& (A : Matrix.{0,0,0} m n ℝ)+ (B : Matrix.{0,0,0} m n ℝ)+ : A + B :=
bconditions
homogenity by
  rw [zero_eq_zero, add_zeroₓ, add_zeroₓ, smul_zero, add_zeroₓ, smul_add]
  rfl
additivity by
  rw [zero_eq_zero, add_zeroₓ, add_zeroₓ, add_assocₓ, add_commₓ B, add_assocₓ A', add_commₓ B']
  simp only [add_assocₓ]
optimality by
  intros A' B' hA hB i j
  apply add_le_add (hA i j) (hB i j)

declare_atom Matrix.sub [affine] (m : Type)& (n : Type)& (A : Matrix.{0,0,0} m n ℝ)+ (B : Matrix.{0,0,0} m n ℝ)- : A - B :=
bconditions
homogenity by
  ext i j
  rw [sub_self]
  change
    κ * (A - B) i j + Zero.zero =
    κ * A i j - κ * B i j + κ * Zero.zero
  rw [_root_.mul_zero, add_zeroₓ, add_zeroₓ, ←mul_sub]
  rfl
additivity by
  rw [sub_self, add_zeroₓ, sub_add_sub_comm]
optimality by
  intros A' B' hA hB i j
  change A i j - B i j ≤ A' i j - B' i j
  apply @sub_le_sub Real _ _ 
    (@OrderedAddCommGroup.to_covariant_class_left_le Real Real.orderedAddCommGroup)
  exact hA i j
  exact hB i j

declare_atom Matrix.mul1 [affine] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)& (B : Matrix.{0,0,0} m m ℝ)? : A ⬝ B :=
bconditions
homogenity by
  rw [zero_eq_zero, Matrix.mul_zero, smul_zero, Matrix.mul_smul]
  rfl
additivity by 
  rw [Matrix.mul_add, zero_eq_zero, Matrix.mul_zero, add_zeroₓ]
optimality le_reflₓ (A ⬝ B)

declare_atom Matrix.mul2 [affine] (m : Type)& (hm : Fintype.{0} m)&
  (A : Matrix.{0,0,0} m m ℝ)? (B : Matrix.{0,0,0} m m ℝ)& : A ⬝ B :=
bconditions
homogenity by
  haveI := @IsScalarTower.right Real Real Real.commSemiring Real.semiring (@Algebra.id Real Real.commSemiring)
  rw [Matrix.smul_mul]
  rw [zero_eq_zero, Matrix.zero_mul, smul_zero]
  rfl
additivity by 
  rw [Matrix.add_mul, zero_eq_zero, Matrix.zero_mul, add_zeroₓ]
optimality le_reflₓ (A ⬝ B)

declare_atom Matrix.mulVec [affine] (n : ℕ)& (m : ℕ)& (M : Matrix.{0,0,0} (Finₓ m) (Finₓ n) ℝ)& (v : Finₓ n → ℝ)? :
  Matrix.mulVecₓ M v :=
bconditions
homogenity by
  simp [zero_eq_zero]
  rw [smul_zero, add_zeroₓ, Matrix.mul_vec_smul]
  rfl
additivity by
  simp [zero_eq_zero, Matrix.mul_vec_add]
optimality le_reflₓ _

declare_atom Matrix.vecMul [affine] (n : ℕ)& (m : ℕ)& (v : Finₓ m → ℝ)? (M : Matrix.{0,0,0} (Finₓ m) (Finₓ n) ℝ)& :
  Matrix.vecMulₓ v M :=
bconditions
homogenity by
  simp [zero_eq_zero]
  haveI := @IsScalarTower.right Real Real Real.commSemiring Real.semiring (@Algebra.id Real Real.commSemiring)
  rw [smul_zero, add_zeroₓ, Matrix.vec_mul_smul]
  rfl
additivity by
  simp [zero_eq_zero, Matrix.add_vec_mul]
optimality le_reflₓ _


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
  simp [Real.posOrthCone, zero_eq_zero]
feasibility
optimality by
  intros x' y' hx hy h
  simp [Real.posOrthCone, zero_eq_zero] at h 
  exact (hx.transₓ h).transₓ hy
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
  intros h
  exact Eq.symm h
vconditionElimination

declare_atom sq [convex] (x : ℝ)? : x ^ 2 := 
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : rotatedSoCone t (1/2) (![x] : Finₓ 1 → ℝ))
solution
  (t := x ^ 2)
solutionEqualsAtom rfl
feasibility
  (c1 : by 
    simp [rotatedSoCone]
    refine ⟨?_, ?_, ?_⟩
    · have : (2 : ℝ) ≠ 0 := by
        apply ne_of_gtₓ
        simp only [(@Nat.cast_zero ℝ _).symm, (@Nat.cast_one ℝ _).symm]
        apply Nat.cast_lt.2
        norm_num
      simp [_root_.mul_assoc, div_mul_cancel _ this]
      have : x ^ 2 = @HPow.hPow ℝ ℕ ℝ instHPow x 2 := 
        by apply Real.rpow_nat_cast
      rw [this]
      exact le_reflₓ _
    · have : x ^ 2 = @HPow.hPow ℝ ℕ ℝ instHPow x 2 := 
        by apply Real.rpow_nat_cast
      rw [this]
      exact sq_nonneg x
    · rw [zero_eq_zero]
      rw [← zero_div 2]
      have : (0 : ℝ) < (2 : ℝ) := by
        simp only [(@Nat.cast_zero ℝ _).symm, (@Nat.cast_one ℝ _).symm]
        apply Nat.cast_lt.2
        norm_num
      have := (@div_le_div_right ℝ _ 0 1 2 this).2
      refine this ?_
      have : ZeroLeOneClass ℝ := @OrderedSemiring.zeroLeOneClass ℝ Real.orderedSemiring
      exact zero_le_one)
optimality by
  have := c1.1
  have two_ne_zero : (2 : ℝ) ≠ 0 := by
    apply ne_of_gtₓ
    simp only [(@Nat.cast_zero ℝ _).symm, (@Nat.cast_one ℝ _).symm]
    apply Nat.cast_lt.2
    norm_num
  simp [_root_.mul_assoc, div_mul_cancel _ two_ne_zero] at this
  have pow_eq_pow : x ^ 2 = @HPow.hPow ℝ ℕ ℝ instHPow x 2 := 
    by apply Real.rpow_nat_cast
  rw [pow_eq_pow]
  exact this
vconditionElimination 

declare_atom exp [convex] (x : ℝ)+ : Real.exp x :=
vconditions
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone x 1 t)
solution (t := exp x)
solutionEqualsAtom by
  rfl;
feasibility (c_exp : by
  simp [expCone]
  apply Or.inl;
  refine ⟨Real.zero_lt_one, ?_⟩
  change x / One.one ≤ x
  rw [div_one]
  apply le_reflₓ _)
optimality by
  intros x' hx
  rw [←exp_iff_expCone] at c_exp
  exact (exp_le_exp.2 hx).transₓ c_exp
vconditionElimination

declare_atom sqrt [concave] (x : ℝ)+ : Real.sqrt x := 
vconditions (cond : 0 ≤ x)
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints 
  (c1 : rotatedSoCone x (1/2) (![t] : Finₓ 1 → ℝ))
solution (t := Real.sqrt x)
solutionEqualsAtom by
  rfl;
feasibility 
  (c1 : by
    unfold rotatedSoCone
    rw [← sq_sqrt cond]
    have : sqrt x ^ 2 = @HPow.hPow ℝ ℕ ℝ instHPow (sqrt x) 2 := 
        by apply Real.rpow_nat_cast
    have sqf := sq.feasibility0 (sqrt x)
    rw [this] at sqf
    simp only [rotatedSoCone] at sqf
    have : 2 = bit0 One.one := rfl
    rw [this, sq_sqrt cond] at sqf
    rw [this, sq_sqrt cond]
    apply sqf)
optimality by
  intros y hy
  have sqopt := sq.optimality t x c1
  apply Real.le_sqrt_of_sq_le
  have : t ^ 2 = @HPow.hPow ℝ ℕ ℝ instHPow t (bit0 One.one) := 
      by apply Real.rpow_nat_cast
  rw [←this]
  apply sqopt.transₓ hy
vconditionElimination (cond : fun _ hx => c1.2.1.transₓ hx)

declare_atom log [concave] (x : ℝ)+ : log x :=
vconditions (cond : 0 < x)
implementationVars (t : ℝ)
implementationObjective t
implementationConstraints (c_exp : expCone t (1) x)
solution (t := log x)
solutionEqualsAtom by 
  rfl;
feasibility (c_exp : by 
  simp [expCone] 
  left
  apply And.intro Real.zero_lt_one
  erw [div_one, Real.exp_log cond]
  exact le_reflₓ _)
optimality by 
  intros x' hx;
  simp [expCone] at c_exp
  cases c_exp with 
  | inl h => 
    rcases h with ⟨_, h⟩
    cases em (0 < x) with 
    | inl h0x => 
      erw [le_log_iff_exp_le (lt_of_lt_of_leₓ h0x hx)]
      erw [div_one] at h
      exact le_transₓ h hx
    | inr h0x => 
      exfalso
      cases (eq_or_lt_of_not_ltₓ h0x) with 
      | inl heq => 
        erw [div_one] at h
        exact lt_irreflₓ 0 (lt_of_lt_of_leₓ (exp_pos t) (heq ▸ h))
      | inr hlt =>
        erw [div_one] at h
        exact lt_irreflₓ 0 (lt_transₓ (lt_of_lt_of_leₓ (exp_pos t) h) hlt)
  | inr h => 
    rcases h with ⟨_, hc, _⟩; 
    exfalso
    exact (zero_ne_one hc.symm)
vconditionElimination 
  (cond : by
    simp [expCone] at c_exp
    apply c_exp.by_cases
    · intro h
      exact fun _ h' => lt_of_lt_of_leₓ (lt_of_lt_of_leₓ (Real.exp_pos _) h.2) h'
    · intro h
      exact False.elim $ zero_ne_one h.2.1.symm)

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
    rw [zero_eq_zero, sub_nonneg]
    apply le_abs_self) 
  (c_neg : by
    unfold posOrthCone
    rw [zero_eq_zero, ← neg_le_iff_add_nonneg' 
      (_inst_3 := @OrderedAddCommGroup.to_covariant_class_left_le Real Real.orderedAddCommGroup)]
    apply neg_abs_le_self 
      (_inst_3 := @OrderedAddCommGroup.to_covariant_class_left_le Real Real.orderedAddCommGroup))
optimality by
  apply abs_le.2
  rw [←sub_nonneg, sub_neg_eq_add, add_commₓ, ←sub_nonneg (b := x)]
  exact ⟨c_neg, c_pos⟩
vconditionElimination

end Real

-- Non-affine atoms on vectors.
section Vec

open Vec

declare_atom Vec.le [concave] (n : Nat)& (x : (Finₓ n) → ℝ)- (y : (Finₓ n) → ℝ)+ : x ≤ y :=
vconditions
implementationVars
implementationObjective Real.Vec.posOrthCone (y - x : (Finₓ n) → ℝ)
implementationConstraints
solution
solutionEqualsAtom by
  unfold Real.Vec.posOrthCone
  rw [← iff_iff_eq]
  constructor
  · intros h i
    rw [←le.solEqAtom]
    apply h
  · intros h i
    change Zero.zero ≤ y i - x i
    rw [le.solEqAtom]
    apply h
feasibility
optimality by
  intros x' y' hx hy h i
  apply le.optimality _ _ _ _ (hx i) (hy i) (h i)
vconditionElimination

declare_atom Vec.exp [convex] (n : Nat)& (x : (Finₓ n) → ℝ)+ : exp x :=
vconditions
implementationVars (t : Finₓ n → ℝ)
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

declare_atom Vec.log [concave] (n : Nat)& (x : (Finₓ n) → ℝ)+ : log x :=
vconditions (cond : ∀ i, 0 < x i)
implementationVars (t : (Finₓ n) → ℝ)
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

declare_atom Vec.abs [convex] (n : Nat)& (x : (Finₓ n) → ℝ)? : abs x :=
vconditions
implementationVars (t : (Finₓ n) → ℝ)
implementationObjective t
implementationConstraints
  (c_pos : Real.Vec.posOrthCone (t - x : (Finₓ n) → ℝ))
  (c_neg : Real.Vec.posOrthCone (t + x : (Finₓ n) → ℝ))
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

-- Non-affine atoms on real variables.
namespace Matrix

declare_atom Matrix.PosSemidef [concave] (m : Type)& (hm : Fintype.{0} m)& (A : Matrix.{0,0,0} m m ℝ)? : Matrix.PosSemidef A :=
vconditions
implementationVars
implementationObjective Real.Matrix.PSDCone A
implementationConstraints
solution
solutionEqualsAtom by simp [Real.Matrix.PSDCone]
feasibility
optimality by simp [Real.Matrix.PSDCone]
vconditionElimination

declare_atom Matrix.logDet [concave] (n : ℕ)& (A : Matrix.{0,0,0} (Finₓ n) (Finₓ n) ℝ)? : Real.log A.det :=
vconditions (hA : A.PosDef)
implementationVars (t : Finₓ n → ℝ) (Y : Matrix (Finₓ n) (Finₓ n) ℝ)
-- The lower left values of `Y` are unused. CVXPy uses a vector `z` instead of a matrix `Y`.
implementationObjective Vec.sum t
implementationConstraints 
  (c_exp : Real.Vec.expCone t 1 Y.diag)
  (c_posdef : Matrix.PosSemidef $
    let Z := Y.toUpperTri;
    let D := Matrix.diagonalₓ Y.diag
    let X := Matrix.fromBlocks D            Z 
                               Z.transpose  A;
    X)
solution 
  (t := 
    have : Decidable (A.PosDef) := Classical.dec _ 
    if h : A.PosDef then Vec.log (LDL.diagEntries h) else 0) 
  (Y :=
    have : Decidable (A.PosDef) := Classical.dec _ 
    if h : A.PosDef then LDL.diag h ⬝ (LDL.lower h).transpose else 0) 
solutionEqualsAtom by
  simp only [dif_pos hA, Vec.sum, Vec.log]
  exact Matrix.LogDetAtom.solution_eq_atom hA
feasibility 
  (c_exp : by
    simp only [Real.Vec.expCone, dif_pos hA]
    intro i
    show 
      Real.expCone ((Real.log (LDL.diagEntries hA i))) 1
        (Matrix.diag (LDL.diag hA ⬝ (LDL.lower hA).transpose) i)
    rw [← Real.exp_iff_expCone, Real.exp_log]
    exact Matrix.LogDetAtom.feasibility_exp hA i
    exact Matrix.LDL.diag_entries_pos hA i)
  (c_posdef : by
    simp only [dif_pos hA]
    apply Matrix.LogDetAtom.feasibility_pos_def' hA rfl rfl rfl)
optimality by
  apply Matrix.LogDetAtom.optimality _ rfl rfl c_posdef
  intro i
  rw [Real.exp_iff_expCone]
  apply c_exp
vconditionElimination 
  (hA : by
    apply Matrix.LogDetAtom.cond_elim _ rfl rfl c_posdef
    · exact t
    · intro i
      rw [Real.exp_iff_expCone]
      apply c_exp)

declare_atom Matrix.abs [convex] (m : Nat)& (n : Nat)& (M : Matrix.{0,0,0} (Finₓ m) (Finₓ n) ℝ)? : Matrix.abs M :=
vconditions
implementationVars (T : Matrix (Finₓ m) (Finₓ n) ℝ)
implementationObjective T
implementationConstraints
  (c_pos : Real.Matrix.posOrthCone (T - M : Matrix (Finₓ m) (Finₓ n) ℝ))
  (c_neg : Real.Matrix.posOrthCone (T + M : Matrix (Finₓ m) (Finₓ n) ℝ))
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
