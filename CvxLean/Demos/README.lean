import CvxLean

/-!
Demo used to make a GIF for README.md.
-/

noncomputable section README

open CvxLean Minimization Real

-- Define.

def p :=
  optimization (x y : ℝ)
    minimize -2 * x
    subject to
      c₁ : 0 ≤ x
      c₂ : 1 < y
      c₃ : log (y - 1) ≤ 2 * sqrt x + 1
      c₄ : 3 * x + 5 * y ≤ 10

-- Transform (proving `p ≡ q`).

equivalence* eqv/q : p := by
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

end README
