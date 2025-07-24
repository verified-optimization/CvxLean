import CvxLean

noncomputable section

open CvxLean Minimization Real BigOperators

def quadratic_problem :=
  optimization (x : ℝ)
    minimize (((x + (-1))) ^ 2 : ℝ)
    subject to
      c1 : 0 ≤ x
      c2 : x ≤ 2

-- Solve the problem directly (applies pre_dcp automatically)
solve quadratic_problem

-- Check the results
#eval quadratic_problem.status
#eval quadratic_problem.solution
#eval quadratic_problem.value

end