import CvxLean.Command.Solve

section Log

open CvxLean Minimization Real

noncomputable def log1 :=
  optimization (x : ℝ) 
    minimize (x)
    subject to 
      h₁ : 10 ≤ log x
      h₂ : 0 < x

solve log1

#print log1.reduced

#eval log1.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval log1.value    -- 22026.464907
#eval log1.solution -- 22026.464907

noncomputable def log2 :=
  optimization (x : ℝ) 
    maximize (log x)
    subject to 
      h₁ : x ≤ 10
      h₂ : 0 < x

set_option trace.Meta.debug true

solve log2

#print log2.reduced

#eval log2.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval log2.value    -- 2.302585
#eval log2.solution -- 10.000000

end Log
