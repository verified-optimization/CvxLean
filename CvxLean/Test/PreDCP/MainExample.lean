import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Convexify

open CvxLean Minimization Real

def p := 
  optimization (x : ℝ)
    minimize (x)
    subject to   
      h1 : 0 < x
      h2 : 1 / (sqrt x) ≤ (exp x)

equivalence eq/q : p := by
  convexify

#print q
-- def q : Minimization ℝ ℝ :=
-- optimization (x : ℝ) 
--   minimize x
--   subject to
--     h1 : 0 < x
--     h2 : -x ≤ log (sqrt x)
  