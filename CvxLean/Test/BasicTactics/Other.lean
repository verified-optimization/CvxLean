import CvxLean.Syntax.Minimization
import CvxLean.Tactic.Basic.CleanUpComp
import CvxLean.Tactic.Basic.RenameVars
import CvxLean.Tactic.Basic.RenameConstrs
import CvxLean.Tactic.Basic.ReorderConstrs
import CvxLean.Tactic.Basic.RemoveConstr
import CvxLean.Tactic.Basic.ConvOpt

noncomputable section BasicTacticTest

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

set_option trace.Meta.debug true
example : Solution <|
    optimization (x y z : ℝ)
      minimize x + y + z
      subject to
        c1 : z = x + y
        c2 : exp x ≤ exp y := by
  rename_constrs [cz, cxy]
  -- conv_constr cxy =>
  --   rw [Real.exp_le_exp]
  -- conv_constr cz =>
  --   rw [add_comm]
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

end BasicTacticTest
