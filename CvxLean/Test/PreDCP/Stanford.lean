import CvxLean.Command.Solve
import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.PreDCP.PreDCP


namespace Stanford

noncomputable section

open CvxLean Minimization Real

/- Exercise 3.67. -/
section E367

def e367 :=
  optimization (x1 x2 x3 x4: ℝ)
    minimize (-(sqrt x1 + sqrt x2 + sqrt x3 + sqrt x4) ^ (2 : ℝ))
    subject to
      h1 : 0.001 ≤ x1
      h2 : 0.001 ≤ x2
      h3 : 0.001 ≤ x3
      h4 : 0.001 ≤ x4

time_cmd reduction red367/dcp367 : e367 := by
  pre_dcp

#print dcp367

solve dcp367

end E367

end

end Stanford
