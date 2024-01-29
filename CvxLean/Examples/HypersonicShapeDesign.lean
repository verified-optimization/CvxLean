import CvxLean

noncomputable section

namespace HypersonicShapeDesign

open CvxLean Minimization Real

def hypersonicShapeDesign (a b : ℝ) :=
  optimization (Δx : ℝ)
    minimize sqrt ((1 / Δx ^ 2) - 1)
    subject to
      h1 : 10e-6 ≤ Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

set_option trace.Meta.debug true

#check Lean.Expr

equivalence eqv/hypersonicShapeDesignConvex (a b : ℝ) (ha : 0 ≤ a) (hb : b < 1) :
    hypersonicShapeDesign a b := by
  pre_dcp

@[optimization_param]
def aₚ : ℝ := 0.05

@[optimization_param]
def bₚ : ℝ := 0.65

-- solve hypersonicShapeDesignConvex aₚ bₚ

-- #eval dqcp2.value
-- #eval dqcp2.solution

end HypersonicShapeDesign

end
