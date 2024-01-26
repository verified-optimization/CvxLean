import CvxLean.Syntax.Minimization
import CvxLean.Tactic.Basic.All
import CvxLean.Command.Equivalence

namespace BasicTacticTest

noncomputable section

open Real CvxLean Minimization

example (f g : ℝ → ℝ) (cs : ℝ → Prop) : Solution ⟨f ∘ g, cs ∘ g⟩ := by
  clean_up_comp
  sorry

opaque a : ℝ
opaque b : ℝ
opaque c : ℝ
opaque d : ℝ

opaque aa : Prop
opaque bb : Prop
opaque cc : Prop
opaque dd : Prop
opaque ee : Prop

example : Solution <|
    optimization (x y z w : ℝ)
      minimize (((c * x) * y) * z) * w
      subject to
        ca : aa
        cb : bb
        cc : cc
        cd : dd
        ce : ee := by
  reorder_constrs [ce, cd, cc, ca, cb]
  rename_constrs [c1, c2, c3, c4, c5]
  sorry

example : Solution <|
    optimization (x y z : ℝ)
      minimize x * y * z
      subject to
        c : z = x + y := by
  rename_vars [y, z, x]
  rename_vars [a, b ,c]
  sorry

example : Solution <|
    optimization (x y : ℝ)
      minimize c * x
      subject to
        c1 : exp y ≤ log (a * sqrt x + b)
        c2 : a * x + b * y = d
        c3 : 0 ≤ x
        c4 : 0 < a * sqrt x + b := by
  rename_vars [y, x]
  reorder_constrs [c2, c1, c4, c3]
  sorry

example : Solution <|
    optimization (x y z : ℝ)
      minimize x + y + z
      subject to
        c1 : z = x + y
        c2 : exp x ≤ exp y := by
  rename_constrs [cz, cxy]
  conv_constr cxy =>
    rw [Real.exp_le_exp]
  conv_constr cz =>
    rw [add_comm]
  conv_obj =>
    rw [add_comm]
  sorry

example : Solution <|
    optimization (x y z : ℝ)
      minimize x + y + z
      subject to
        cz : z = x + y
        cz' : z = x + y
        cz'' : z ≤ x + 4 := by
  remove_constr cz' by { exact cz }
  rename_constrs [czz, czz2]
  sorry

example : Solution <|
    optimization (x y z : ℝ)
      minimize x + y + z
      subject to
        c1 : 1 + 2 + 3 ≤ x
        c2 : 2 + 3 + 4 ≤ y := by
  conv_opt =>
    norm_num
  sorry

equivalence eqv/q :
    optimization (x y z : ℝ)
      minimize x + y + z
      subject to
        c1 : 1 + 2 + 3 ≤ x
        c2 : 2 + 3 + 4 ≤ y := by
  rename_vars [a, b, c]
  conv_obj =>
    rw [add_assoc]
  conv_constr c1 =>
    norm_num1

equivalence eqv2/q1 :
    optimization (x y z a b c : ℝ)
      minimize sqrt (x ^ (2 : ℕ))
      subject to
        c₁ : x ≤ y
        c₂ : 0 ≤ x + 1 + 2 + 34
        c₃ : 0 ≤ x
        c₄ : 0 ≤ b + c
        c₅ : 0 ≤ z + a
        c₆ : 0 ≤ x + 2 * z := by
  rw_obj =>
    exact sqrt_sq c₃
  rw_constr c₂ =>
    ring_nf
    rfl

end

end BasicTacticTest
