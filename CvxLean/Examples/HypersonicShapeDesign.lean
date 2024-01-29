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

lemma aₚ_nonneg : 0 ≤ aₚ := by
  unfold aₚ; norm_num

@[optimization_param]
def bₚ : ℝ := 0.65

lemma bₚ_lt_one : bₚ < 1 := by
  unfold bₚ; norm_num

@[simp high]
lemma one_sub_bₚ_nonpos : 0 ≤ 1 - bₚ := by
  unfold bₚ; norm_num

solve hypersonicShapeDesignConvex aₚ bₚ aₚ_nonneg bₚ_lt_one

#eval hypersonicShapeDesignConvex.value
#eval hypersonicShapeDesignConvex.solution

end HypersonicShapeDesign

end
