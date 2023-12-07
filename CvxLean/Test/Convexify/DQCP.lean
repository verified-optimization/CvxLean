import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.Convexify.Basic
import CvxLean.Tactic.Convexify.Convexify
import CvxLean.Test.Util.TimeCmd

namespace DQCP

noncomputable section

open CvxLean Minimization Real

/- TODO: where does this example come from?  -/
section QCP1

def qcp1 :=
  optimization (x y : ℝ)
    minimize (-y)
    subject to
      h1 : 1 ≤ x
      h2 : x ≤ 2
      h3 : 0 ≤ y
      h4 : sqrt ((2 * y) / (x + y)) ≤ 1

time_cmd reduction redqcp1/dqcp1 : qcp1 := by
  convexify

#print dqcp1
-- def dqcp1 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ)
--   minimize y
--   subject to
--     h1 : 1 ≤ x
--     h2 : x ≤ 2
--     h3 : 0 ≤ y
--     h4 : y * 2 - x ≤ y

solve dqcp1

#eval dqcp1.value -- -2.000000

end QCP1

/- -/
section QCP2

def hypersonicShapeDesign (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize sqrt (1 / (Δx ^ 2) - 1)
    subject to
      h1 : 0 < Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

time_cmd reduction redqcp2/dqcp2 : hypersonicShapeDesign 0.35 0.65 := by
  unfold hypersonicShapeDesign;
  convexify
  dcp --TODO: This has 0 ≤ Δx ?????

-- solve dqcp2

end QCP2

end

end DQCP
