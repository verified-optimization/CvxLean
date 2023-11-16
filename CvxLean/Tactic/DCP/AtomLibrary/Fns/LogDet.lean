import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Sum
import CvxLean.Tactic.DCP.AtomLibrary.Fns.PosSemidef
import CvxLean.Tactic.DCP.AtomLibrary.Fns.FromBlocks
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Diag
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Diagonal
import CvxLean.Tactic.DCP.AtomLibrary.Fns.Transpose
import CvxLean.Tactic.DCP.AtomLibrary.Fns.ToUpperTri
import CvxLean.Lib.Math.LogDet

namespace CvxLean

open Matrix

declare_atom Matrix.logDet [concave] (n : ℕ)&
(A : Matrix.{0,0,0} (Fin n) (Fin n) ℝ)? : Real.log A.det :=
vconditions (hA : A.PosDef)
implementationVars (t : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ)
-- The lower left values of `Y` are unused. CVXPY uses a vector `z` instead of a
-- matrix `Y`.
implementationObjective Vec.sum t
implementationConstraints
  (c_exp : Real.Vec.expCone t 1 Y.diag)
  (c_posdef : Matrix.PosSemidef <|
    let Z := Y.toUpperTri;
    let D := Matrix.diagonal Y.diag
    let X := Matrix.fromBlocks D  Z
                               Zᵀ A;
    X)
solution
  (t :=
    have : Decidable (A.PosDef) := Classical.dec _
    if h : A.PosDef then Vec.log (LDL.diagEntries h) else 0)
  (Y :=
    have : Decidable (A.PosDef) := Classical.dec _
    if h : A.PosDef then (LDL.diag h) * (LDL.lower h)ᵀ else 0)
solutionEqualsAtom by
  simp only [dif_pos hA, Vec.sum, Vec.log]
  rw [Matrix.LogDetAtom.solution_eq_atom hA]
  congr
feasibility
  (c_exp : by
    simp only [Real.Vec.expCone, dif_pos hA]
    intro i
    show Real.expCone ((Real.log (LDL.diagEntries hA i))) 1
      (Matrix.diag ((LDL.diag hA) * (LDL.lower hA)ᵀ) i)
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
    exact Matrix.LogDetAtom.cond_elim
      (A := A) (t := t) (Y := Y) ht rfl rfl (by convert c_posdef))

end CvxLean
