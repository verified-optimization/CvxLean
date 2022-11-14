import CvxLean.Lib.Minimization 
import CvxLean.Syntax.Minimization
import CvxLean.Lib.Approximation.Real 

open CvxLean Minimization

def prob : Minimization ℝ ℝ := 
  optimization (x : ℝ)
    minimize (x) 
    subject to
      h : x ≥ 0

def solDyadic : Dyadic := Dyadic.mk 0 0 

noncomputable def sol : ℝ := solDyadic.toReal

noncomputable def probSol : Solution prob := by 
  simp only [prob]
  apply Solution.mk sol
  { simp only [constraints, sol, solDyadic];
    simp only [Real.commRing];
    sorry } 
  sorry
