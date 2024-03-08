import CvxLean

/-!
This demo was used for Lean Together 2024, see the video here:
<https://www.youtube.com/watch?v=GNOXmt5A_MQ>
-/

namespace LT2024

noncomputable section

open CvxLean Minimization Real

/- First example. -/

def p₁ :=
  optimization (x y : ℝ)
    maximize sqrt (x - y)
    subject to
      c1 : y = 2 * x - 3
      c2 : x ^ (2 : ℝ) ≤ 2
      c3 : 0 ≤ x - y

#check p₁

-- Apply DCP transformation and call solver.
solve p₁

#eval p₁.status
#eval p₁.solution
#eval p₁.value


/- Second example. -/

def p₂ :=
  optimization (x : ℝ)
    minimize (x)
    subject to
      c1 : 1 / 1000 ≤ x
      c2 : 1 / sqrt x ≤ exp x

-- solve p₂

-- set_option trace.Meta.debug true

-- Equivalence mode.
equivalence eqv₂/q₂ : p₂ := by
  pre_dcp

solve q₂

#print q₂.conicForm

#eval q₂.status
#eval q₂.solution
#eval q₂.value


/- Third example (geometric programming). -/

/-- Maximizing the volume of a box.
See: https://www.cvxpy.org/examples/dgp/max_volume_box.html -/
def p₃ (Awall Aflr α β γ δ : ℝ) :=
  optimization (h w d : ℝ)
    minimize (1 / (h * w * d))
    subject to
      c1 : 0 < h
      c2 : 0 < w
      c3 : 0 < d
      c4 : 2 * (h * w + h * d) ≤ Awall
      c5 : w * d ≤ Aflr
      c6 : α ≤ h / w
      c7 : h / w ≤ β
      c8 : γ ≤ d / w
      c9 : d / w ≤ δ

equivalence* eqv₃/q₃ : p₃ 100 10 0.5 2 0.5 2 := by
  change_of_variables! (h') (h ↦ exp h')
  change_of_variables! (w') (w ↦ exp w')
  change_of_variables! (d') (d ↦ exp d')
  pre_dcp

solve q₃

#print q₃.conicForm

#eval q₃.status
#eval q₃.solution
#eval q₃.value

#check eqv₃

def p₃.solution := eqv₃.backward_map q₃.solution

#eval p₃.solution

def h := p₃.solution.1
def w := p₃.solution.2.1
def d := p₃.solution.2.2

#eval h * w * d

#eval 2 * (h * w + h * d) ≤ 100
#eval w * d ≤ 10
#eval 0.5 ≤ h / w
#eval h / w ≤ 2
#eval 0.5 ≤ d / w
#eval d / w ≤ 2

end

end LT2024
