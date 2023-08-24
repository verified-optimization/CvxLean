import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section GP

open CvxLean Minimization Real

/- This problem is not DGP because the number on the right-hand side of the
constraint is negative. In fact, this problem is DCP because we can expand the
power atom. -/
section AlmostDGP1

def agp1 :=
    optimization (x : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : x ^ 2 ≤ -10.123

reduction red1/dcp1 : agp1 := by
  map_exp
  convexify
  exact done

#print dcp1
-- def dcp1 : Minimization ℝ ℝ :=
-- optimization (x : ℝ)
--   minimize x
--   subject to
--     _ : exp (x * 2) ≤ -(10123 / 1000)

end AlmostDGP1

/- This problem is not DGP because the number on the right-hand side of the
constraint is negative. It is also not DCP because it does not follow the
product-free rules. -/
section AlmostDGP2

def agp2 :=
    optimization (x y : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : 0 < y
        h3 : x * y ≤ -5.382

reduction red2/dcp2 : agp2 := by
  map_exp
  convexify
  exact done

#print dcp2
-- def dcp2 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ)
--   minimize x
--   subject to
--     _ : exp (x + y) ≤ -(2691 / 500)

end AlmostDGP2

/- This problem is not DGP because -6 * y / z is not a positive monomial. It is
not DCP either. -/
section AlmostDGP3

def agp3 :=
  optimization (x y z : ℝ)
    minimize (x / y)
    subject to
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 ≤ x
      h5 : x ≤ 3
      h6 : x ^ 2 ≤ sqrt x - 6 * y / z
      h7 : x * y = z

reduction red3/dcp3 : agp3 := by
  map_exp
  convexify
  exact done

#print dcp3
-- def dcp3 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ)
--   minimize exp (x - y)
--   subject to
--     _ : log 2 ≤ x
--     _ : exp x ≤ 3
--     _ : exp (2 * x - 1 / 2 * x) + 6 * exp (y + (-(x * (1 / 2)) - z)) ≤ 1
--     _ : x + y = z

end AlmostDGP3
