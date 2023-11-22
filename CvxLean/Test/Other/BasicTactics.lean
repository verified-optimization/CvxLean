import CvxLean.Syntax.Minimization
import CvxLean.Tactic.Basic.DomainEquiv
import CvxLean.Tactic.Basic.Rename
import CvxLean.Tactic.Basic.CleanUpComp
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Tactic.Basic.ReorderConstr
import CvxLean.Tactic.Basic.ShowVars
import CvxLean.Tactic.Basic.RenameConstr
import CvxLean.Tactic.Basic.RemoveConstr
import CvxLean.Lib.Missing.Vec


namespace BasicTacticTest

open Real
open CvxLean
open Minimization

noncomputable opaque a : ℝ
noncomputable opaque b : ℝ
noncomputable opaque c : ℝ
noncomputable opaque d : ℝ

-- set_option pp.CvxLean.labels true
-- set_option pp.optMinimization true
-- set_option pp.all true

opaque aa : Prop
opaque bb : Prop
opaque cc : Prop
opaque dd : Prop
opaque ee : Prop

noncomputable example : Solution $
  optimization (x y z w : ℝ)
    minimize (((c * x) * y) * z) * w
    subject to
      a : aa
      b : bb
      c : cc 
      d : dd 
      e : ee := by
  reorder_constr [e, d, c, a, b]
  sorry

noncomputable example : Solution $
  optimization (x y : ℝ)
    minimize c * x
    subject to
      e : exp y ≤ log (a * sqrt x + b)
      l : a * x + b * y = d
      hsqrt : 0 ≤ x
      hlog : 0 < a * sqrt x + b := by
  domain_equiv Equiv.refl ({** ℝ ** w **} × {** ℝ ** y **})
  domain_equiv (Equiv.mk 
    (fun (p : {** ℝ ** y **} × {** ℝ ** x **}) => (p.2, p.1)) 
    (fun p => (p.2, p.1)) sorry sorry)
  sorry

noncomputable example : Solution $
  optimization (x y : ℝ)
    minimize c * x
    subject to
      e : exp y ≤ log (a * sqrt x + b)
      l : a * x + b * y = d
      hsqrt : 0 ≤ x
      hlog : 0 < a * sqrt x + b := by
  apply Minimization.domain_equiv (Equiv.mk (fun (p : {** ℝ ** y**} × {** ℝ ** x**}) => ((p.2, p.1) : {** ℝ ** x**} × {** ℝ ** y**})) (fun p => (p.2, p.1)) sorry sorry)
  clean_up_comp
  sorry

noncomputable example : Solution $
  optimization (x y z : ℝ)
    minimize x + y + z
    subject to
      cz : z = x + y
      cxy : exp x ≤ exp y := by
  reorder_constr [cxy, cz]
  conv_constr cxy =>
    rw [Real.exp_le_exp]
  conv_constr cz =>
    rw [add_comm]
  conv_obj => 
    rw [add_comm]
  sorry

noncomputable example : Solution $
  optimization (x y z : ℝ)
    minimize x + y + z
    subject to
      cz : z = x + y
      cz' : z = x + y := by
  remove_constr cz'
  · exact h
  rename_constr [czz]
  sorry

end BasicTacticTest