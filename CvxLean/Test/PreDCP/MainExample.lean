import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.PreDCP.PreDCP

/-!
Example that we often use as a simple motivating example for automated pre-DCP transformations.
-/

namespace MainExample

noncomputable section

open CvxLean Minimization Real

def p :=
  optimization (x : ℝ)
    minimize (x)
    subject to
      h1 : 1 / 1000 ≤ x
      h2 : 1 / (sqrt x) ≤ (exp x)

time_cmd equivalence eq/q : p := by
  pre_dcp

#check congrArg

#print q
-- optimization (x : ℝ)
--   minimize x
--   subject to
--     h1 : 1 / 1000 ≤ x
--     h2 : exp (-x) ≤ sqrt x

solve q

#print q.conicForm
-- optimization (x : ℝ) (t.0 : ℝ) (t.1 : ℝ)
--   minimize x
--   subject to
--     _ : nonnegOrthCone (t.1 - t.0)
--     _ : expCone (-x) 1 t.0
--     _ : nonnegOrthCone (x - 1 / 1000)
--     _ : rotatedSoCone x (1 / 2) ![t.1]

#eval q.value -- 0.426303

end

end MainExample
