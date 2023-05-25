import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Basic

section GP

open CvxLean Minimization Real

noncomputable def gp :=
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x
      h5 : x <= 3 
      h6 : x^2 + 3 * y / z <= x^0.5
      h7 : x * y = z

reduction red/gp2 : gp := by 
  unfold gp
  map_objFun_log
  map_exp
  exact done

end GP
