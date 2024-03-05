import CvxLean.Command.Solve
import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.PreDCP.PreDCP

/-!
Examples from quasiconvex programming that can be directly rewritten into DCP form by `pre_dcp`.
-/

namespace DQCP

noncomputable section

open CvxLean Minimization Real

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
  pre_dcp

#print dqcp1
-- optimization (x : ℝ) (y : ℝ)
--   minimize y
--   subject to
--     h1 : 1 ≤ x
--     h2 : x ≤ 2
--     h3 : 0 ≤ y
--     h4 : y * 2 - x ≤ y

solve dqcp1

#print dqcp1.conicForm -- ...
#eval dqcp1.value      -- -2.000000
#eval dqcp1.solution   -- (2.000000, 2.000000)

end QCP1

section QCP2

/-! Adapted from https://www.cvxpy.org/examples/dqcp/hypersonic_shape_design.html.
See `CvxLean/Examples/HypersonicShapeDesign.lean` for a complete analysis. -/

def qcp2 (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize sqrt (1 / (Δx ^ (2 : ℝ)) - 1)
    subject to
      h1 : 10e-6 ≤ Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ (2 : ℝ)) ≤ 0

time_cmd equivalence redqcp2/dqcp2 : qcp2 0.05 0.65 := by
  pre_dcp

solve dqcp2

#print dqcp2.conicForm -- ...
#eval dqcp2.value      -- 0.021286
#eval dqcp2.solution   -- 0.989524

end QCP2

section QCP3

def qcp3 :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      c₁ : 0.001 <= y
      c₂ : x / y ≤ 3
      c₃ : x = 12
      c₄ : y ≤ 6

time_cmd reduction redqcp3/dqcp3 : qcp3 := by
  pre_dcp

solve dqcp3

#print dqcp3.conicForm -- ...
#eval dqcp3.value      -- 0.000000
#eval dqcp3.solution   -- (12.000000, 4.000000)

end QCP3

section QCP4

def qcp4 :=
  optimization (x : ℝ)
    minimize -x
    subject to
      c₁ : sqrt ((x + 1) ^ 2 + 4) / sqrt (x ^ 2 + 100) ≤ 1
      c₂ : 10 ≤ x

time_cmd reduction redqcp4/dqcp4 : qcp4 := by
  pre_dcp

solve dqcp4

#print dqcp4.conicForm -- ...
#eval dqcp4.value      -- -47.500000
#eval dqcp4.solution   -- 47.500000

end QCP4

end

end DQCP
