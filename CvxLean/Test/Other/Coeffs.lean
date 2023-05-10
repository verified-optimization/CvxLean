import CvxLean.Syntax.Minimization
import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.Solver.Float.Coeffs

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
