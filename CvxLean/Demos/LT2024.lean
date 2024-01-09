import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.Convexify.Convexify
import CvxLean.Tactic.ChangeOfVariables.ChangeOfVariables
import CvxLean.Tactic.ChangeOfVariables.Basic

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
def p₃ (Awall Aflr α β γ δ: ℝ) :=
  optimization (h w d : ℝ)
    minimize (1 / (h * w * d))
    subject to
      c1 : 0 < h
      c2 : 0 < w
      c3 : 0 < d
      c4 : 2 * (h * d + w * d) ≤ Awall
      c5 : w * d ≤ Aflr
      c6 : α ≤ h / w
      c7 : h / w ≤ β
      c8 : γ ≤ d / w
      c9 : d / w ≤ δ

--solve p₃

equivalence eqv₃/q₃ : p₃ 100 10 0.5 2 0.5 2 := by
  change_of_variables (h') (h ↦ exp h')
  change_of_variables (w') (w ↦ exp w')
  change_of_variables (d') (d ↦ exp d')
  -- TODO: remove positive constraints. Tactic remove_trivial_constraints
  simp only [exp_pos, true_and]
  convexify

solve q₃
-- solve p₃ that's what I really want

#print q₃.reduced

#eval q₃.status
#eval q₃.solution
#eval q₃.value

#check eqv₃.psi
-- TODO: Float maps so that we can chain equivalences.
-- or change solve.
-- We need:
-- * All tactics to work smoothly on equivalence and reduciton modes (wrapper).
-- * Deal with map_exp and everything in cov/basic.
-- * Tactics to clean up problem.
-- * The wrapper should also deal with unfolding and not closing goals, using transitivity.
-- * dcp needs to return an equivalence.
--
-- Ideas:
-- * EquivalenceTacticM, ReductionTacticM, RelaxationTacitcM.

end

end LT2024
