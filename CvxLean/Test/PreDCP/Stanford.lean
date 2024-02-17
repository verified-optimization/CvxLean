import CvxLean.Command.Solve
import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.PreDCP.PreDCP

namespace Stanford

noncomputable section

open CvxLean Minimization Real

/- Exercise 3.36 (c). -/
section Stan1

def stan1 :=
  optimization (x y : ℝ)
    minimize log (exp (2 * x + 3) + exp (4 * y + 5))
    subject to
      h1 : 0 ≤ x

time_cmd reduction red1/dcp1 : stan1 := by
  pre_dcp

#print dcp1

solve dcp1

end Stan1

/- Exercise 3.38 (e), which is exercise 3.67 with n = 2. -/
section Stan2

def stan2 :=
  optimization (x1 x2 : ℝ)
    minimize (-(sqrt x1 + sqrt x2) ^ (2 : ℝ))
    subject to
      h1 : 0.001 ≤ x1
      h2 : 0.001 ≤ x2

time_cmd reduction red2/dcp2 : stan2 := by
  pre_dcp

#print dcp2

solve dcp2

end Stan2

/- Exercise 3.67 with n = 3. -/
section Stan3

def stan3 :=
  optimization (x1 x2 x3 : ℝ)
    minimize (-(sqrt x1 + sqrt x2 + sqrt x3) ^ (2 : ℝ))
    subject to
      h1 : 0.001 ≤ x1
      h2 : 0.001 ≤ x2
      h3 : 0.001 ≤ x3

time_cmd reduction red3/dcp3 : stan3 := by
  pre_dcp

#print dcp3

solve dcp3

end Stan3

/- Exercise 3.67 with n = 4. -/
section Stan4

def stan4 :=
  optimization (x1 x2 x3 x4 : ℝ)
    minimize (-(sqrt x1 + sqrt x2 + sqrt x3 + sqrt x4) ^ (2 : ℝ))
    subject to
      h1 : 0.001 ≤ x1
      h2 : 0.001 ≤ x2
      h3 : 0.001 ≤ x3
      h4 : 0.001 ≤ x4

time_cmd reduction red4/dcp4 : stan4 := by
  pre_dcp

#print dcp4

solve dcp4

end Stan4

end

end Stanford
