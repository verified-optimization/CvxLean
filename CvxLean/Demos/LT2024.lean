import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.Convexify.Convexify
import CvxLean.Tactic.ChangeOfVariables.ChangeOfVariables

namespace LT2024

noncomputable section

open CvxLean Minimization Real

def p₁ :=
  optimization (x y : ℝ)
    maximize sqrt (x - y)
    subject to
      c1 : y = 2 * x - 3
      c2 : x ^ (2 : ℝ) ≤ 2 -- TODO: remove ": ℝ"
      c3 : x ≤ 3

solve p₁

#eval p₁.status
#eval p₁.solution
#eval p₁.value

def p₂ :=
  optimization (x : ℝ)
    minimize (x)
    subject to
      c1 : 1 / 1000 ≤ x
      c2 : 1 / sqrt x ≤ exp x

-- solve p₂

equivalence eqv₂/q₂ : p₂ := by
  convexify

solve q₂

#print q₂.reduced

#eval q₂.status
#eval q₂.solution
#eval q₂.value

/-- See https://www.cvxpy.org/examples/dgp/max_volume_box.html -/
def p₃ (α : ℝ) :=
  optimization (h w d : ℝ)
    minimize (1 / (h * w * d))
    subject to
      c1 : 0 < h
      c2 : 0 < w
      c3 : 0 < d
      c4 : 2 * (h * d + w * d) ≤ 100
      c5 : w * d ≤ 10
      c6 : 0.5 ≤ h / w
      c7 : h / w ≤ 0.5
      c8 : 5 ≤ d / w
      c9 : d / w ≤ 6

--solve p₃

equivalence eqv₃/q₃ : p₃ 0.5 := by
  unfold p₃
  change_of_variables (h') (h ↦ exp h')
  change_of_variables (w') (w ↦ exp w')
  change_of_variables (d') (d ↦ exp d')
  convexify

solve q₃

#print q₃.reduced

#eval q₃.status
#eval q₃.solution
#eval q₃.value

end

end LT2024
