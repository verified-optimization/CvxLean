import CvxLean.Command.Equivalence
import CvxLean.Command.Reduction
import CvxLean.Tactic.Basic.ChangeOfVariables

/-!
Testing changes of variables.
-/

open CvxLean

noncomputable section ChangeOfVariablesInstances

instance : ChangeOfVariables (fun (x : ℝ) => Real.exp x) := by
  infer_instance

instance : ChangeOfVariables (fun (x : ℝ) => x + 1) := by
  infer_instance

instance : ChangeOfVariables (fun (x : ℝ) => x - 1) := by
  infer_instance

instance : ChangeOfVariables (fun (x : ℝ) => x⁻¹) := by
  infer_instance

instance : ChangeOfVariables (fun (x : ℝ) => 3 * x) := by
  infer_instance

instance : ChangeOfVariables (fun (x : ℝ)  => 3 / x) := by
  infer_instance

end ChangeOfVariablesInstances

def p :=
  optimization (x y : ℝ)
    minimize (x + y)
    subject to
      h : 0 < x

equivalence eqv/q1 : p := by
  change_of_variables (u) (x ↦ Real.exp u)

#print q1

equivalence eqv2/q2 : p := by
  change_of_variables (u) (y ↦ u + (1 : ℝ))

#print q2

reduction eqv3/q3 : p := by
  change_of_variables (u) (x ↦ (1 : ℝ) / u)

#print q3
