import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Convexify

open CvxLean Minimization Real

def mainExample := 
  optimization (x : ℝ)
    minimize (x)
    subject to   
      h1 : 0 < x
      h2 : 1 / (sqrt x) ≤ (exp x)

equivalence eq/mainExample' : mainExample := by
  unfold mainExample
  convexify
