import CvxLean.Syntax.Minimization
import CvxLean.Tactic.Visualize.Plot

section Plot

open CvxLean Minimization Real

noncomputable def prob1Var :=
  optimization (x : ℝ) 
    minimize (exp x)
    subject to 
      h : 10 ≤ x

set_option trace.Meta.debug true

#plot_1_var prob1Var [[1.0, 10.0]]

noncomputable def prob2Vars :=
  optimization (x y : ℝ) 
    minimize (exp x) + y
    subject to 
      h1 : 1 ≤ x
      h2 : 1 ≤ y

set_option trace.Meta.debug true

#plot_2_vars prob2Vars [[1.0, 2.0], [1.0, 10.0]]

end Plot


