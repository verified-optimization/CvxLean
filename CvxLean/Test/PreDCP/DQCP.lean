import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section DQCP

open CvxLean Minimization Real

def dqcp1 :=
  optimization (x : ℝ) 
    minimize (x)
    subject to 
      h1 : 0 < x
      h3 : sqrt (x / (x + 1)) ≤ 1

reduction red1/dcp1 : dqcp1 := by
  convexify

#print dcp1

solve dcp1

#eval dcp1.value
#eval dcp1.solution

end DQCP
