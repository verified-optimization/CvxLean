import CvxLean

noncomputable section

open CvxLean Minimization Real BigOperators

def simple_lp :=
  optimization (x : ℝ) (y : ℝ)
    minimize (x + 2 * y)
    subject to
      c1 : 0 ≤ x
      c2 : 0 ≤ y
      c3 : (x + y) ≤ 1

-- Solve the problem directly (applies pre_dcp automatically)
solve simple_lp

-- Check the results
#eval simple_lp.status
#eval simple_lp.solution
#eval simple_lp.value

end