import CvxLean.Tactic.DCP.Atoms
import CvxLean.Lib.Cones
import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec
import CvxLean.Lib.Math.Data.Matrix
import CvxLean.Lib.Math.LogDet
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.LDL
import CvxLean.Syntax.Minimization

namespace CvxLean

-- Affine operations on matrices.
section MatrixAffine

open Matrix

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

-- instance : HSMul ℝ Prop Prop where
--   hSMul k P := ∃ a b : ℝ, (P ↔ a ≤ b) ∧ k • a ≤ k • b

-- instance : HAdd Prop Prop Prop where
--   hAdd P Q := ∃ a b c d : ℝ, (P ↔ a ≤ b) ∧ (Q ↔ c ≤ d) ∧ (a + c ≤ b + d)

declare_atom le [convex_set] (x : ℝ)- (y : ℝ)+ : x ≤ y :=
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

declare_atom eq [convex_set] (x : ℝ)? (y : ℝ)? : x = y :=
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


-- declare_atom wrong [convex] (x : ℝ)? : abs x :=
-- vconditions
-- implementationVars (t : ℝ)
-- implementationObjective t
-- implementationConstraints
--   (c_pos : posOrthCone (t - x ^ 2))
-- solution (t := abs x)
-- solutionEqualsAtom rfl
-- feasibility
--   (c_pos : sorry)
-- optimality by sorry
-- vconditionElimination

-- -- Convex
-- class IsRealAtom (f : ℝ → ℝ) where
--   (impObj : ℝ × ℝ → ℝ)
--   (impObjAffine : ∀ (x : ℝ) (t : ℝ) (s : ℝ), s * impObj ⟨x, t⟩ = impObj ⟨s * x, s * t⟩)
--   (impConstr : ℝ × ℝ → Prop)
--   (sol : ℝ → ℝ)
--   (solEqAtom : ∀ (x : ℝ), impObj ⟨x, sol x⟩ = f x)
--   (feasibility : ∀ (x : ℝ), impConstr ⟨x, sol x⟩)
--   (optimality : ∀ (x : ℝ) (t : ℝ), impConstr ⟨x, t⟩ → f x ≤ impObj ⟨x, t⟩)

-- declare_atom IsSimpleRealAtom.impConstr [cone] (f : ℝ → ℝ)? (hatom : IsRealAtom f)? (x : ℝ)? (t : ℝ)? (s : ℝ)? : hatom.impConstr ⟨x / s, t / s⟩ :=
-- optimality le_refl _

-- declare_atom IsSimpleRealAtom.impObj [convex] (f : ℝ → ℝ)? (hatom : IsRealAtom f)? (x : ℝ)? (t : ℝ)? (s : ℝ)? : hatom.impObj ⟨x, t⟩ :=
-- vconditions
-- implementationVars (z : ℝ)
-- implementationObjective sorry
-- implementationConstraints
--   (c : True)
-- solution (z := sorry)
-- solutionEqualsAtom sorry
-- feasibility
--   (c : trivial)
-- optimality by
--   sorry
-- vconditionElimination

-- #check EuclideanDomain.mul_div_cancel_left

-- -- IsConvexReducible?

-- Another option: declare_atom_unsafe, and do everything in meta.

-- declare_atom perspective [convex] (f : ℝ → ℝ)? (x : ℝ)? (hatom : IsRealAtom f)? (s : ℝ)? : s * f (x / s) :=
-- vconditions (cond : 0 < s)
-- implementationVars (t : ℝ)
-- implementationObjective (hatom.impObj ⟨x, t⟩)
-- implementationConstraints
--   (c : hatom.impConstr ⟨x / s, t / s⟩)
--   (cs : 0 < s)
-- solution (t := s * hatom.sol (x / s))
-- solutionEqualsAtom by {
--   simp
--   sorry
-- }
-- feasibility
--   (c : by {
--     dsimp
--     simp [mul_div_cancel_left (a := s) (hatom.sol (x / s)) (ne_of_lt cond).symm]
--     exact hatom.feasibility (x / s)
--   })
--   (cs : cond)
-- optimality by {
--     have := hatom.optimality (x / s) (t / s) c
--     sorry
--   }
-- vconditionElimination
--   (cond : cs)

end Real

-- Non-affine atoms on vectors.
section Vec

open Vec

declare_atom Vec.le [convex_set] (n : Nat)& (x : (Fin n) → ℝ)- (y : (Fin n) → ℝ)+ : x ≤ y :=
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

declare_atom Matrix.PosSemidef [convex_set]
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

set_option trace.Meta.debug true in
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
  dsimp at c_posdef
  -- NOTE: Not matching instances, hence `convert` not `exact`.
  have h := Matrix.LogDetAtom.optimality
    (A := A) (t := t) (Y := Y) ht rfl rfl (by convert c_posdef)
  convert h
vconditionElimination
  (hA : by
    have ht : ∀ (i : Fin n), Real.exp (t i) ≤ Matrix.diag Y i := by
      intro i
      rw [Real.exp_iff_expCone]
      apply c_exp
    exact Matrix.LogDetAtom.cond_elim (A := A) (t := t) (Y := Y) ht rfl rfl (by convert c_posdef))

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
