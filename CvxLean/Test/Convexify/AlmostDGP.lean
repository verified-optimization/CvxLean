import CvxLean.Command.Solve
import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.Convexify.Convexify
import CvxLean.Tactic.Basic.RemoveTrivialConstrs

namespace AlmostGP

noncomputable section

open CvxLean Minimization Real

/- This problem is not DGP because of -10.123 -/
section AlmostDGP1

def agp1 :=
    optimization (x : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : x ^ (2 : ℝ) - 10.123 ≤ 0

time_cmd reduction reda1/dcpa1 : agp1 := by
  change_of_variables (u) (x ↦ Real.exp u)
  remove_trivial_constrs
  convexify

#print dcpa1
-- def dcpa1 : Minimization ℝ ℝ :=
-- optimization (x : ℝ)
--   minimize x
--   subject to
--     h2 : exp (x * 2) - 10123 / 1000 ≤ 0

solve dcpa1

end AlmostDGP1

/- This problem is not DGP because of -5.382. -/
section AlmostDGP2

def agp2 :=
    optimization (x y : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : 0 < y
        h3 : x * y - 5.382 ≤ 0

set_option trace.Meta.debug true
time_cmd reduction reda2/dcpa2 : agp2 := by
  change_of_variables! (u) (x ↦ Real.exp u)
  change_of_variables! (v) (y ↦ Real.exp v)
  convexify

#print dcpa2
-- def dcpa2 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ)
--   minimize x
--   subject to
--     h3 : exp (x + y) - 2691 / 500 ≤ 0

solve dcpa2

end AlmostDGP2

/- This problem is not DGP because -6 * y / z is not a positive monomial. -/
section AlmostDGP3

def agp3 :=
  optimization (x y z : ℝ)
    minimize (x + y + z)
    subject to
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 ≤ x
      h5 : x ≤ 3
      h6 : sqrt x ≤ x ^ (2 : ℝ) - 6 * y / z
      h7 : x * y = z

time_cmd reduction reda3/dcpa3 : agp3 := by
  map_exp
  convexify

#print dcpa3
-- def dcpa3 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ)
--   minimize exp y + (exp x + exp z)
--   subject to
--     h4 : log 2 ≤ x
--     h5 : x ≤ log 3
--     h6 : 6 * exp (y - z - x * 2) ≤ 1 - exp (x * -(3 / 2))
--     h7 : x + y = z

solve dcpa3

end AlmostDGP3

/- This problem is not DGP because -x and -y are not positive monomials. -/
section AlmostDGP4

def agp4 :=
  optimization (x y : ℝ)
    minimize (1 / (x * y))
    subject to
      h1 : 0 < x
      h2 : 0 < y
      h3 : x * y ≤ 2 - x - y

time_cmd reduction reda4/dcpa4 : agp4 := by
  map_exp
  convexify

#print dcpa4
-- def dcpa4 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ)
--   minimize -(x + y)
--   subject to
--     h3 : exp x ≤ 2 - exp (x + y) - exp y

solve dcpa4

end AlmostDGP4

-- /- This problem is not convex. -/
-- section AlmostDGP5

-- def agp5 :=
--   optimization (x y : ℝ)
--     minimize (x * y)
--     subject to
--       h1 : 0 < x
--       h2 : 0 < y
--       h3 : x * y ≤ 2 + x - y

-- reduction reda5/dcpa5 : agp5 := by
--   map_exp
--   try { convexify } -- Should fail.

-- end AlmostDGP5

-- /- This problem is not convex. -/
-- section AlmostDGP6

-- def agp6 :=
--   optimization (x y : ℝ)
--     minimize (x * y)
--     subject to
--       h1 : 0 < x
--       h2 : 0 < y
--       h3 : sqrt (x * y - y) ≤ 1

-- reduction reda6/dcpa6 : agp6 := by
--   map_exp
--   try { convexify } -- Should fail.

-- end AlmostDGP6

end

end AlmostGP
