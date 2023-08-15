import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section Rules

open CvxLean Minimization Real

def invExpObj := 
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to 
      h : 1 ≤ x

reduction invExpObjRedAuto/invExpObjAuto : invExpObj := by
  unfold invExpObj
  convexify
  exact done

-- TODO(RFM): Use this lemma instead of exp_neg.
lemma Real.exp_neg2 : ∀ x : ℝ, exp (-x) = 1 / exp x := by
  intro x
  rw [Real.exp_neg, inv_eq_one_div]

reduction invExpObjRedManual/invExpObjManual : invExpObj := by
  unfold invExpObj
  map_objFun_log
  simp only [←Real.exp_neg2]

end Rules 