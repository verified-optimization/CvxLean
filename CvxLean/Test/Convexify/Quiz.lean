import CvxLean.Command.Equivalence
import CvxLean.Tactic.DCP.AtomLibrary.All
import CvxLean.Tactic.Convexify.Convexify
import CvxLean.Test.Util.TimeCmd

namespace Quiz

noncomputable section

open CvxLean Minimization Real

def quiz1 :=
  optimization (x : ℝ)
    minimize (x⁻¹⁻¹)
    subject to
      h : 0 < x

time_cmd equivalence eq1/dcpquiz1 : quiz1 := by
  convexify

def quiz2 :=
  optimization (x y : ℝ)
    minimize (-(log (exp (log (x + 42)) + exp (log y))))
    subject to
      h₁ : 0 < x
      h₂ : 0 < y

time_cmd equivalence eq2/dcpquiz2 : quiz2 := by
  convexify

def quiz3 :=
  optimization (x : ℝ)
    minimize ((sqrt x) ^ 2)
    subject to
      h : 0 ≤ x

time_cmd equivalence eq3/dcpquiz3 : quiz3 := by
  convexify

def quiz4 :=
  optimization (x : ℝ)
    minimize (-(abs (sqrt (abs (x + 42)))))
    subject to
      h : 0 ≤ x

time_cmd equivalence eq4/dcpquiz4 : quiz4 := by
  convexify

def quiz5 :=
  optimization (x : ℝ)
    minimize (1 / exp (x + 42))
    subject to
      h : 1000 ≤ x -- irrelevant

time_cmd equivalence eq5/dcpquiz5 : quiz5 := by
  convexify

def quiz6 :=
  optimization (x : ℝ)
    minimize (-(log ((364 * x) ^ 2)))
    subject to
      h : 0 ≤ x

time_cmd equivalence eq6/dcpquiz6 : quiz6 := by
  convexify

def quiz7 :=
  optimization (x : ℝ)
    minimize ((sqrt ((x + 2) * (1 / x))) ^ 2)
    subject to
      h : 0 < x

time_cmd equivalence eq7/dcpquiz7 : quiz7 := by
  convexify

def quiz8 :=
  optimization (x : ℝ)
    minimize (-(log (abs x)))
    subject to
      h : 0 ≤ x

time_cmd equivalence eq8/dcpquiz8 : quiz8 := by
  convexify

def quiz9 :=
  optimization (x y : ℝ)
    minimize (1 / (((x⁻¹) ^ 2) / (y⁻¹)))
    subject to
      h₁ : 0 < x
      h₂ : 0 < y

time_cmd equivalence eq9/dcpquiz9 : quiz9 := by
  convexify

def quiz10 :=
  optimization (x : ℝ)
    minimize ((log (exp x)) ^ 2)
    subject to
      h : 0 ≤ x

time_cmd equivalence eq10/dcpquiz10 : quiz10 := by
  convexify

end

end Quiz
