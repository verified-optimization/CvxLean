import CvxLean.Command.Solve

/-!
Some quadratic programs.
-/

section SO

open CvxLean Minimization Real

noncomputable def so1 :=
  optimization (x y : ℝ)
    maximize sqrt (x - y)
    subject to
      c1 : y = 2 * x - 3
      c2 : x ^ (2 : ℝ) ≤ 2
      c3 : 0 ≤ x - y

solve so1

#print so1.conicForm

#eval so1.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval so1.value    -- 2.101003
#eval so1.solution -- (-1.414214, -5.828427)

def so2 :=
  optimization (x : ℝ)
    minimize (x)
    subject to
      hx : 1 / 1000 ≤ x
      h : exp (-x) ≤ sqrt x

solve so2

#print so2.conicForm

#eval so2.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval so2.value    -- 0.426303
#eval so2.solution -- 0.426303

end SO
