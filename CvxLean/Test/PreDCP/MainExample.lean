import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section MainExample

open CvxLean Minimization Real

def p := 
  optimization (x : ℝ)
    minimize (x)
    subject to   
      h1 : 0.001 ≤ x
      h2 : 1 / (sqrt x) ≤ (exp x)

reduction eq/q : p := by
  convexify

solve q

#print q.reduced

#print q
-- def q : Minimization ℝ ℝ :=
-- optimization (x : ℝ) 
--   minimize x
--   subject to
--     h1 : 0 < x
--     h2 : exp (-x) ≤ sqrt x


end MainExample 
