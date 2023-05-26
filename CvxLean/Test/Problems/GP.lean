import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section GP

open CvxLean Minimization Real

def gp :=
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x
      h5 : x <= 3 
      h6 : x^2 + 3 * y / z <= sqrt x
      h7 : x * y = z

set_option trace.Meta.debug true

reduction red/gp2 : gp := by 
  unfold gp
  map_exp
  convexify
  norm_num
  exact done

#print gp2
-- def gp2 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize x - y
--   subject to
--     _ : log 2 ≤ x
--     _ : x ≤ log 3
--     _ : exp (x * (3 / 2)) + exp (y - z - 1 / 2 * x) * 3 ≤ 1
--     _ : x + y = z

end GP
