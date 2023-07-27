import CvxLean.Syntax.Minimization
import CvxLean.Tactic.Visualize.Plot

section Plot

open CvxLean Minimization Real

noncomputable def plotExp :=
  optimization (x : ℝ) 
    minimize (exp x)
    subject to 
      h : 10 ≤ x

set_option trace.Meta.debug true

#plot1D plotExp

end Plot


