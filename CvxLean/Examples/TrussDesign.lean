import CvxLean

noncomputable section

namespace TrussDesign

open CvxLean Minimization Real

-- Height range (distance between the upper bearing's `y` coordinate and the joint's `y` coordinate;
-- which is the same as the distance from the lower bearing's `y` coordinate, as the truss is
-- assumed to be symmetric along the joint's `x` line).
variable (hmin hmax : ℝ)
variable (hmin_pos : 0 < hmin) (hmin_le_hmax : hmin ≤ hmax)

-- Width range (distance between the bearings' `x` coordinate and the joint's `x` coordinate).
variable (wmin wmax : ℝ)
variable (wmin_pos : 0 < wmin) (wmin_le_wmax : wmin ≤ wmax)

-- Maximum outer radius of the bar.
variable (Rmax : ℝ)

-- Maximum allowable stress.
variable (σ : ℝ)

-- Vertical downward force on the joint.
variable (F₁ : ℝ)

-- Horizontal left-to-right force on the joint.
variable (F₂ : ℝ)

set_option trace.Meta.debug true
set_option pp.rawOnError true

def trussDesign  :=
  optimization (h w r R : ℝ) with A := 2 * π * (R ^ 2 - r ^ 2)
    minimize 2 * A * sqrt (w ^ 2 + h ^ 2)
    subject to
      c_r    : 0 < r
      c_F₁   : F₁ * sqrt (w ^ 2 + h ^ 2) / (2 * h) ≤ 0.5 * A
      c_F₂   : F₂ * sqrt (w ^ 2 + h ^ 2) / (2 * w) ≤ 0.5 * A
      c_hmin : hmin ≤ h
      c_hmax : h ≤ hmax
      c_wmin : wmin ≤ w
      c_wmax : w ≤ wmax
      c_R_lb : 1.1 * r ≤ R
      c_R_ub : R ≤ Rmax

#print trussDesign

set_option maxHeartbeats 1000000
-- time_cmd reduction red8/dcp8 : gp8 := by
--   change_of_variables! (h') (h ↦ exp h')
--   change_of_variables! (w') (w ↦ exp w')
--   change_of_variables! (A') (A ↦ exp A')
--   change_of_variables! (r') (r ↦ exp r')
--   pre_dcp

-- hmin = wmin = 1, hmax = wmax = 100, Rmax = 10, σ = 0.5.
-- F1 = 10 F2 = 20

end TrussDesign

end
