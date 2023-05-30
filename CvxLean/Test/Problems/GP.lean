import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section GP

open CvxLean Minimization Real

lemma test : Solution (
    optimization (x : ℝ)
      minimize (x)
      subject to
        hx : 0 < x
        h : x ^ 2 ≤ -10.123
) := by
  map_exp
  convexify
  sorry

lemma test2 : Solution (
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x 
      h6 : x^2 + 6 * y / z <= sqrt x
      h7 : x * y = z) := by 
  map_exp
  convexify
  sorry

-- https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (4)
-- NOTE(RFM): `maximize` does not work because it is set to `Neg.neg`.
def gp1 :=
  optimization (x y z : ℝ) 
    minimize 1 / (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x
      h5 : x <= 3 
      h6 : x^2 + 3 * y / z <= sqrt x
      h7 : x / y = z^2

set_option trace.Meta.debug true

reduction red/dcp1 : gp1 := by 
  map_exp
  convexify
  exact done

#print dcp1
-- def dcp1 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize y - x
--   subject to
--     _ : log 2 ≤ x
--     _ : exp x ≤ 3
--     _ : exp (x * (3 / 2)) + 3 * exp (y + (-(x * (1 / 2)) - z)) ≤ 1
--     _ : x - y = 2 * z

def gp2 :=
  optimization (h w d : ℝ) 
    minimize (1 / h) * (1 / w) * (1 / d)
    subject to 
      h1 : 0 < h
      h2 : 0 < w
      h3 : 0 < d
      h4 : 2 * (h * d + w * d) ≤ 10 -- A_wall

reduction red2/dcp2 : gp2 := by
  map_exp
  convexify
  exact done

#print dcp2
-- def dcp2 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (h : ℝ) (w : ℝ) (d : ℝ) 
--   minimize -h + -w - d
--   subject to
--     _ : 2 * exp (d + h) + 2 * exp (d + w) ≤ 10

def gp3 := 
  optimization ( x y z : ℝ) 
    --minimize (x ^ (-1)) * y ^ (-1 / 2) * z ^ (-1) + 2.3 * x * z + 4 * x * y * z
    minimize (1 / x) * (1 / sqrt y) * (1 / z) + (2.3) * x * z + 4 * x * y * z
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      --h4 : (1 / 3) * x ^ (-2) * y ^ (-2) + (4 / 3) * y ^ (1 / 2) * z ^ (-1) ≤ 1
      h4 : (1 / 3) * (1 / (x ^ 2)) * (1 / (y ^ 2)) + (4 / 3) * (sqrt y) * (1 / z) ≤ 1
      h5 : x + 2 * y + 3 * z ≤ 1
      h6 : (1 / 2) * x * y = 1

set_option maxHeartbeats 1000000
reduction red3/dcp3 : gp3 := by
  map_exp
  convexify
  exact done

#print dcp3
-- def dcp3 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize exp (-(y * (1 / 2)) - x - z) + (23 * (exp (z + x) / 10) + 4 * exp (y + (z + x)))
--   subject to
--     _ : 1 / 3 * exp (-(y * 2) + -(2 * x)) + 1 / 3 * (4 * exp (y * (1 / 2) - z)) ≤ 1
--     _ : exp x + (exp y * 2 + exp z * 3) ≤ 1
--     _ : y + (x - log 2) = 0

end GP
