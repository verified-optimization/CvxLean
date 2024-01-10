import CvxLean.Command.Solve

section Exp

open CvxLean Minimization Real

noncomputable def exp1 :=
  optimization (x : ℝ)
    maximize (x)
    subject to
      h : exp x ≤ 10

solve exp1

#print exp1.reduced

#eval exp1.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval exp1.value    -- 2.302585
#eval exp1.solution -- 2.302585

noncomputable def exp2 :=
  optimization (x : ℝ)
    minimize (exp x)
    subject to
      h : 10 ≤ x

solve exp2

#print exp2.reduced

#eval exp2.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval exp2.value    -- 22026.464907
#eval exp2.solution -- 10.000000

end Exp
