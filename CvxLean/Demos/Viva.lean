import CvxLean

/-!
Demo for my PhD viva (31st of May, 2024).
-/

namespace Viva

noncomputable section

open CvxLean Minimization Real


/- Simple use case. -/

def p₁ :=
  optimization (x y : ℝ)
    maximize sqrt (x - y)
    subject to
      c₁ : y = 2 * x - 3
      c₂ : x ^ 2 ≤ 2
      c₃ : 0 ≤ x - y

#check p₁

solve p₁

#print p₁.conicForm

#eval p₁.status
#eval p₁.solution
#eval p₁.value


/- Example with some user-guided transformations. -/

def p₂ :=
  optimization (x y : ℝ)
    minimize -2 * x
    subject to
      c₁ : 0 ≤ x
      c₂ : 1 < y
      c₃ : log (y - 1) ≤ 2 * sqrt x + 1
      c₄ : 3 * x + 5 * y ≤ 10

-- Transform (proving `p₂ ≡ q`).
equivalence* eqv/q : p₂ := by
  change_of_variables! (v) (y ↦ v + 1)
  change_of_variables! (w) (v ↦ exp w)
  remove_constr c₂ =>
    field_simp; arith
  -- Make DCP-compliant automatically:
  -- pre_dcp
  -- Or, manually:
  rw_constr c₃ into (w ≤ 2 * sqrt x + 1) =>
    field_simp

#print q

#check eqv

-- Solve (proving `q ≡ q.conicForm`).
solve q

#print q.conicForm

#eval q.status
#eval q.value
#eval q.solution

#eval eqv.backward_map q.solution

end

end Viva
