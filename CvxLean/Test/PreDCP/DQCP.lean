import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section DQCP

open CvxLean Minimization Real

def dqcp1 :=
  optimization (x y : ℝ) 
    minimize (y)
    subject to 
      h1 : 1 ≤ x
      h2 : x ≤ 2 
      h3 : 0 ≤ y
      h4 : sqrt ((2 * y) / (x + y)) ≤ 1

reduction red1/dcp1 : dqcp1 := by
  convexify

#print dcp1

solve dcp1

#eval dcp1.value
#eval dcp1.solution

end DQCP
