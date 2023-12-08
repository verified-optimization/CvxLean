import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
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

-- def hypersonicShapeDesign (a b : ℝ) :=
--   optimization (Δx : ℝ)
--     minimize sqrt (1 / (Δx ^ 2) - 1)
--     subject to
--       h1 : 0 < Δx
--       h2 : Δx ≤ 1
--       h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

-- time_cmd equivalence redqcp2/dqcp2 : hypersonicShapeDesign 0.05 0.65 := by
--   unfold hypersonicShapeDesign
--   convexify

-- TODO: the issue comes from the redundant exp constraint that we use
-- as a positivity trick.

def hypersonicShapeDesign (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize Δx ^ (-2) - 1
    subject to
      h1 : 0 < Δx
      h2 : Δx ≤ 1
      h3 : (1/7) * (1 / Δx) ≤ sqrt (1 - Δx ^ 2)

time_cmd equivalence redqcp2/dqcp2 : hypersonicShapeDesign 0.05 0.65 := by
  unfold hypersonicShapeDesign

-- TODO: Error in solve:
-- Lean server printed an error:
-- PANIC at Lean.Expr.mvarId! Lean.Expr:1067:14: mvar expected
-- PANIC at Lean.MetavarContext.getDecl Lean.MetavarContext:398:17: unknown metavariable
solve dqcp2

#print dqcp2.reduced
-- def dqcp2.reduced : Minimization (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) ℝ :=
-- optimization (Δx : ℝ) (t₀.0 : ℝ) (t₁.1 : ℝ) (t.2 : ℝ) (y'.3 : ℝ) (t.0.4 : ℝ) (t.5 : ℝ) (t.6 : ℝ)
--   minimize t₀.0 - 1
--   subject to
--     _ : posOrthCone (1 - Δx)
--     _ : posOrthCone (0 - 7 / 20 * (t.2 - t.6))
--     _ : soCone (Δx + t₁.1) ![Δx - t₁.1, 2]
--     _ : soCone (t₀.0 + 1) ![t₀.0 - 1, 2 * t₁.1]
--     _ : posOrthCone (t₀.0 - 0)
--     _ : posOrthCone (t₁.1 - 0)
--     _ : posOrthCone (Δx - 0)
--     _ : soCone (Δx + t.2) ![Δx - t.2, 2 * 1]
--     _ : posOrthCone (t.2 - 0)
--     _ : posOrthCone (Δx - t.0.4)
--     _ : expCone y'.3 1 t.0.4
--     _ : rotatedSoCone t.5 (1 / 2) ![Δx]
--     _ : rotatedSoCone (1 - t.5) (1 / 2) ![t.6]


    -- _ : posOrthCone (t.6 - t.2 / 20 / (7 / 20))

-- TODO: this is wrong.
#eval dqcp2.value
#eval dqcp2.solution

end QCP2

end

end DQCP
