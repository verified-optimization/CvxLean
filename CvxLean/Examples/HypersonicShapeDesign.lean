import CvxLean
import CvxLean.Command.Util.TimeCmd

noncomputable section

namespace HypersonicShapeDesign

open CvxLean Minimization Real

-- Height of rectangle.
variable (a : ℝ)

-- Width of rectangle.
variable (b : ℝ)

def hypersonicShapeDesign :=
  optimization (Δx : ℝ)
    minimize sqrt ((1 / Δx ^ 2) - 1)
    subject to
      h₁ : 10e-6 ≤ Δx
      h₂ : Δx ≤ 1
      h₃ : a * (1 / Δx) - (1 - b) * sqrt (1 - Δx ^ 2) ≤ 0

equivalence' eqv₁/hypersonicShapeDesignConvex (a b : ℝ) (ha : 0 ≤ a) (hb₁ : 0 ≤ b) (hb₂ : b < 1) :
    hypersonicShapeDesign a b := by
  pre_dcp

#print hypersonicShapeDesignConvex

@[optimization_param]
def aₚ : ℝ := 0.05

@[simp high]
lemma aₚ_nonneg : 0 ≤ aₚ := by
  unfold aₚ; norm_num

@[optimization_param]
def bₚ : ℝ := 0.65

lemma bₚ_nonneg : 0 ≤ bₚ := by
  unfold bₚ; norm_num

lemma bₚ_lt_one : bₚ < 1 := by
  unfold bₚ; norm_num

@[simp high]
lemma one_sub_bₚ_nonneg : 0 ≤ 1 - bₚ := by
  unfold bₚ; norm_num

time_cmd solve hypersonicShapeDesignConvex aₚ bₚ aₚ_nonneg bₚ_nonneg bₚ_lt_one

#print hypersonicShapeDesignConvex.reduced

-- Final width of wedge.
def width := eqv₁.backward_map aₚ.float bₚ.float hypersonicShapeDesignConvex.solution

#eval width -- 0.989524

#eval aₚ.float * (1 / width) - (1 - bₚ.float) * Float.sqrt (1 - width ^ 2) ≤ 0
#eval aₚ.float * (1 / width) - (1 - bₚ.float) * Float.sqrt (1 - width ^ 2) ≤ 0.000001

-- Final height of wedge.
def height := Float.sqrt (1 - width ^ 2)

#eval height -- 0.144368

-- Final L/D ratio.
def ldRatio := 1 / (Float.sqrt ((1 / width ^ 2) - 1))

#eval ldRatio -- 6.854156

-- While the above is good enough, we simplify the problem further by performing a change of
-- variables and simplifying appropriately.

equivalence' eqv₂/hypersonicShapeDesignSimpler (a b : ℝ) (ha : 0 ≤ a) (hb₁ : 0 ≤ b)
    (hb₂ : b < 1) : hypersonicShapeDesignConvex a b ha hb₁ hb₂ := by
  change_of_variables (z) (Δx ↦ sqrt z)
  conv_constr h₁ =>
    rewrite [le_sqrt' (by norm_num)]; norm_num
  conv_constr h₂ =>
    rewrite [sqrt_le_iff]; norm_num
  rw_constr h₃ =>
    have hz : 0 ≤ z := by arith
    have h_one_sub_z : 0 ≤ 1 - z := by arith
    rewrite [rpow_two (sqrt a), sq_sqrt ha, rpow_two (sqrt z), sq_sqrt hz]
    rewrite [div_le_iff (by arith)]
    have hlhs : 0 ≤ a / sqrt z := div_nonneg ha (sqrt_nonneg _)
    have hrhs : 0 ≤ sqrt (1 - z) * (1 - b) := mul_nonneg (sqrt_nonneg _) (by arith)
    rewrite [← pow_two_le_pow_two hlhs hrhs]
    rewrite [div_rpow ha (sqrt_nonneg _), rpow_two (sqrt z), sq_sqrt hz]
    rewrite [mul_rpow (sqrt_nonneg _) (by arith), rpow_two (sqrt (1 - z)), sq_sqrt h_one_sub_z]
    rewrite [← mul_one_div, ← inv_eq_one_div, mul_comm (1 - z) _]
    rfl
  rename_constrs [h₁, h₂, h₃]
  rw_obj =>
    rewrite [rpow_neg (sqrt_nonneg _), rpow_two (sqrt z), sq_sqrt (by arith)]
    rfl

#print hypersonicShapeDesignSimpler

time_cmd solve hypersonicShapeDesignSimpler aₚ bₚ aₚ_nonneg bₚ_nonneg bₚ_lt_one

#print hypersonicShapeDesignSimpler.reduced

-- Final width of wedge.
def width' :=
  eqv₁.backward_map aₚ.float bₚ.float <|
    eqv₂.backward_map aₚ.float bₚ.float hypersonicShapeDesignSimpler.solution

#eval width' -- 0.989524

#eval aₚ.float * (1 / width') - (1 - bₚ.float) * Float.sqrt (1 - width' ^ 2) ≤ 0

-- Final height of wedge.
def height' := Float.sqrt (1 - width' ^ 2)

#eval height' -- 0.144371

-- Final L/D ratio.
def ldRatio' := 1 / (Float.sqrt ((1 / width' ^ 2) - 1))

#eval ldRatio' -- 6.854031

end HypersonicShapeDesign

end
