import CvxLean.Command.Reduction
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real

noncomputable section HypersonicShapeDesign

open Matrix

def problem (a b : ℝ) :=
  optimization (Δx : ℝ) 
    minimize Real.sqrt (1 / (Δx ^ 2) - 1)
    subject to 
      h1 : 0 < Δx
      h2 : Δx ≤ 1
      h3 : a * (1 / Δx) - (1 - b) * Real.sqrt (1 - Δx ^ 2) ≤ 0 

#check sq_le_sq

reduction red/problem₂ (a b : ℝ) : problem a b := by 
  unfold problem 
  apply map_objective ℝ ℝ _ (fun x => x ^ 2)
  { rintro r s ⟨hr1, hr2, _hr3⟩ ⟨hs1, hs2, _hs3⟩ h 
    have hr2nn : 0 < r ^ 2 := rpow_two _ ▸ pow_pos hr1 2
    have hr2leone : r ^ 2 ≤ 1 := rpow_two _ ▸ pow_le_one _ hr1.le hr2
    have hinvr2subone : 0 ≤ 1 / r ^ 2 - 1 := by 
      rw [le_sub_iff_add_le, zero_add, le_div_iff hr2nn, one_mul]
      exact hr2leone
    have hs2nn : 0 < s ^ 2 := rpow_two _ ▸ pow_pos hs1 2
    have hs2leone : s ^ 2 ≤ 1 := rpow_two _ ▸ pow_le_one _ hs1.le hs2
    have hinvs2subone : 0 ≤ 1 / s ^ 2 - 1 := by 
      rw [le_sub_iff_add_le, zero_add, le_div_iff hs2nn, one_mul]
      exact hs2leone
    simp only [rpow_two (Real.sqrt _)] at h
    rw [sq_sqrt hinvr2subone] at h
    rw [sq_sqrt hinvs2subone] at h
    exact sqrt_le_sqrt h }
  simp only [Function.comp]
  apply rewrite_objective (g := fun x => (1 / (x ^ 2) - 1))
  { rintro x ⟨h1, h2, _h3⟩
    have hx2nn : 0 < x ^ 2 := rpow_two _ ▸ pow_pos h1 2
    have hx2leone : x ^ 2 ≤ 1 := rpow_two _ ▸ pow_le_one _ h1.le h2
    have hinvx2subone : 0 ≤ 1 / x ^ 2 - 1 := by 
      rw [le_sub_iff_add_le, zero_add, le_div_iff hx2nn, one_mul]
      exact hx2leone
    simp only [rpow_two (Real.sqrt _)]
    rw [sq_sqrt hinvx2subone]
    simp only [rpow_two] }
  apply rewrite_constraints (ds := fun x => 
    0 < x ∧ x ≤ 1 ∧ a ^ 2 * (1 / x) ^ 2 ≤ (1 - b) ^ 2 * (1 - x ^ 2))
  { intros x
    sorry }
  exact done


def hypersonicShapeDesign₂ (a b : ℝ) :=
  optimization (Δx : ℝ) 
    minimize 1 / (Δx ^ 2) - 1
    subject to 
      h1 : 0 < Δx
      h2 : Δx ≤ 1
      h3 : a ^ 2 * (1 / (Δx  ^ 2)) + (1 - b) ^ 2 * (Δx ^ 2) ≤ (1 - b) ^ 2

def hypersonicShapeDesign₃ (a b : ℝ) :=
  optimization (Δx2 : ℝ) 
    minimize 1 / Δx2 - 1
    subject to 
      h2 : Δx2 ≤ 1
      h3 : a ^ 2 * (1 / Δx2) + (1 - b) ^ 2 * Δx2 ≤ (1 - b) ^ 2

example : Solution (hypersonicShapeDesign₂ 0.5 0.5) := by 
  unfold hypersonicShapeDesign₂
  dcp
  sorry

example : Solution (hypersonicShapeDesign₃ 0.5 0.5) := by 
  unfold hypersonicShapeDesign₃
  dcp
  sorry


end HypersonicShapeDesign