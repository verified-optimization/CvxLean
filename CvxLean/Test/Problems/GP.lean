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

set_option trace.Meta.debug true in
set_option maxHeartbeats 1000000 in
reduction red/gp2 : gp := by 
  unfold gp
  map_exp
  convexify
  norm_num
  exact done

end GP
