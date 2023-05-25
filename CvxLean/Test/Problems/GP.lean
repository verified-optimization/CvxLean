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
  have heq₁ : Solution
    (optimization (x : ℝ) (y : ℝ) (z : ℝ) 
      minimize Real.log (exp x / exp y)
      subject to
        h1 : 0 < exp x
        h2 : 0 < exp y
        h3 : 0 < exp z
        h4 : 2 ≤ exp x
        h5 : exp x ≤ 3
        h6 : exp x ^ 2 + 3 * exp y / exp z ≤ exp x ^ OfScientific.ofScientific 5 true 1
        h7 : exp x * exp y = exp z
      ) = 
    Solution
    (optimization (x : ℝ) (y : ℝ) (z : ℝ) 
      minimize Real.log (exp (x - y))
      subject to
        h1 : 0 < exp x
        h2 : 0 < exp y
        h3 : 0 < exp z
        h4 : 2 ≤ exp x
        h5 : exp x ≤ 3
        h6 : exp x ^ 2 + 3 * exp y / exp z ≤ exp x ^ OfScientific.ofScientific 5 true 1
        h7 : exp x * exp y = exp z
    ) := by {
      internally_rewrite ←Real.exp_sub
    }
  exact done

end GP
