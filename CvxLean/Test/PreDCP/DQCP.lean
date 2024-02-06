import CvxLean.Command.Solve
import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.PreDCP.PreDCP


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

#eval dqcp1.value -- -2.000000

end QCP1

/- https://www.cvxpy.org/examples/dqcp/hypersonic_shape_design.html -/
section QCP2

def hypersonicShapeDesign (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize sqrt (1 / (Δx ^ (2 : ℝ)) - 1)
    subject to
      h1 : 10e-6 ≤ Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ (2 : ℝ)) ≤ 0

time_cmd equivalence redqcp2/dqcp2 : hypersonicShapeDesign 0.05 0.65 := by
  pre_dcp

solve dqcp2

#print dqcp2.reduced
-- optimization (Δx : ℝ) (t₀.0 : ℝ) (t₁.1 : ℝ) (t.2 : ℝ) (y'.3 : ℝ) (t.4 : ℝ) (t.5 : ℝ)
--   minimize t₀.0 - 1
--   subject to
--     _ : posOrthCone (1 - Δx)
--     _ : posOrthCone (7 / 20 * t.5 - t.2 / 20)
--     _ : soCone (Δx + t₁.1) ![Δx - t₁.1, 2]
--     _ : soCone (t₀.0 + 1) ![t₀.0 - 1, 2 * t₁.1]
--     _ : posOrthCone (t₀.0 - 0)
--     _ : posOrthCone (t₁.1 - 0)
--     _ : posOrthCone (Δx - 0)
--     _ : soCone (Δx + t.2) ![Δx - t.2, 2 * 1]
--     _ : posOrthCone (t.2 - 0)
--     _ : rotatedSoCone t.4 (1 / 2) ![Δx]
--     _ : rotatedSoCone (1 - t.4) (1 / 2) ![t.5]

#eval dqcp2.value
#eval dqcp2.solution

end QCP2

end

end DQCP
