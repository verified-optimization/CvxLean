import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Test.Util.TimeCmd

namespace MainExample

noncomputable section

open CvxLean Minimization Real

def p := 
  optimization (x : ℝ)
    minimize (x)
    subject to   
      h1 : 0.001 ≤ x
      h2 : 1 / (sqrt x) ≤ (exp x)

time_cmd equivalence eq/q : p := by
  convexify

#print q
-- def q : Minimization ℝ ℝ :=
-- optimization (x : ℝ) 
--   minimize x
--   subject to
--     h1 : 1 / 1000 ≤ x
--     h2 : exp (-x) ≤ sqrt x

solve q

#print q.reduced
-- def q.reduced : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (t.0 : ℝ) (t.1 : ℝ) 
--   minimize x
--   subject to
--     _ : posOrthCone (t.1 - t.0)
--     _ : expCone (-x) 1 t.0
--     _ : posOrthCone (x - 1 / 1000)
--     _ : rotatedSoCone x (1 / 2) ![t.1]

#eval q.value -- 0.426303

end

end MainExample 
