import CvxLean.Command.Solve

section SO

open CvxLean Minimization Real

-- Example from TACAS paper.

noncomputable def so1 := 
  optimization (x y : ℝ) 
    maximize sqrt (x - y)
    subject to
      c1 : y = 2 * x - 3
      c2 : x ^ 2 ≤ 2
      c3 : 0 ≤ x - y

solve so1

#print so1.reduced

#eval so1.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval so1.value    -- 2.101003
#eval so1.solution -- (-1.414214, -5.828427)

end SO
