import CvxLean.Syntax.Minimization
import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.Solver.Float.Coeffs

attribute [-instance] Nat.hasSub String.hasToString String.hasAppend 
  Nat.hasToString Bool.inhabited Ne.decidable Prod.inhabited 
  String.hasDecidableEq Nat.hasAdd Fin.decidableEq 

attribute [-instance] Real.hasLt Real.hasLe Real.hasOne Real.hasZero Real.hasMul 
  Real.linearOrderedField Real.hasNatCast Real.hasAdd Real.addCommGroup 
  Real.hasNeg Real.hasSub Real.ring Real.addMonoid Real.monoid
  Real.monoidWithZero Real.module Real.addCommMonoid Real.hasPow 
  Real.linearOrder Real.conditionallyCompleteLinearOrder Real.orderedSemiring
  Real.hasSup

section Coeffs

open CvxLean Minimization

set_option trace.Meta.debug true

noncomputable def testVecExp1 : Solution $
  optimization (x y : Fin 1 → ℝ)
    minimize (0 : ℝ)
    subject to
      c0 : Real.Vec.expCone y x 1 := by
  coeffs
  sorry

noncomputable def testMatrix1 : Solution $
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (0 : ℝ)
    subject to
      c0 : Real.Matrix.PSDCone (2 • X) := by
  coeffs
  sorry

noncomputable def testVecExpAndMatrix1 : Solution $
  optimization (x y : Fin 1 → ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (0 : ℝ)
    subject to
      c0 : Real.Vec.expCone y x 1
      c1 : Real.Matrix.PSDCone (2 • X) := by
  coeffs
  sorry

noncomputable def testMatrixPosOrth : Solution $
  optimization (x : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ) 
    minimize (0 : ℝ)
    subject to 
      c0 : Real.Matrix.posOrthCone (2 • X)
       := by 
  coeffs 
  sorry

end Coeffs
