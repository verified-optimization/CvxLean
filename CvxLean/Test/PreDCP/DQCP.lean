import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Test.Util.TimeCmd

namespace DQCP

noncomputable section

open CvxLean Minimization Real

def qcp :=
  optimization (x y : ℝ) 
    minimize (-y)
    subject to 
      h1 : 1 ≤ x
      h2 : x ≤ 2 
      h3 : 0 ≤ y
      h4 : sqrt ((2 * y) / (x + y)) ≤ 1

time_cmd reduction redqcp/dcpq : qcp := by
  convexify

#print dcpq
-- def dcpq : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) 
--   minimize y
--   subject to
--     h1 : 1 ≤ x
--     h2 : x ≤ 2
--     h3 : 0 ≤ y
--     h4 : y * 2 ≤ y + x

solve dcpq

#eval dcpq.value -- -2.000000

end

end DQCP
