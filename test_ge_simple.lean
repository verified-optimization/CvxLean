import CvxLean

noncomputable section

open CvxLean Minimization Real BigOperators

def test_ge_simple :=
  optimization (x : ℝ) (y : ℝ)
    minimize (x + y)
    subject to
      c1 : x ≤ 3
      c2 : y ≤ 8
      c3 : x ≥ 1
      c4 : y ≥ 2

-- Solve the problem directly (applies pre_dcp automatically)
solve test_ge_simple

-- Check the results
#eval test_ge_simple.status
#eval test_ge_simple.solution
#eval test_ge_simple.value

end
