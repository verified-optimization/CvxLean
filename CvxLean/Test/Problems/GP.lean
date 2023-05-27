import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section GP

open CvxLean Minimization Real

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
--   minimize x - y
--   subject to
--     _ : log 2 ≤ x
--     _ : exp x ≤ 3
--     _ : exp (x * (3 / 2)) + 3 * exp (y - z - 1 / 2 * x) ≤ 1
--     _ : x - y = 2 * z

end GP
