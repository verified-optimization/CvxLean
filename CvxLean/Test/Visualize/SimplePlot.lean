import CvxLean.Syntax.Minimization
import CvxLean.Tactic.Visualize.Plot

section Plot

-- set_option trace.Meta.debug true

open CvxLean Minimization Real

noncomputable def prob1Var :=
  optimization (x : ℝ) 
    minimize (exp x)
    subject to 
      h : 5 ≤ x

#plot_1_var prob1Var [[1.0, 10.0]]

noncomputable def prob2Vars :=
  optimization (x y : ℝ) 
    minimize (exp x) + y
    subject to 
      h1 : x ≤ y

#plot_2_vars prob2Vars [[0.0, 2.0], [0.0, 2.0]]

end Plot


