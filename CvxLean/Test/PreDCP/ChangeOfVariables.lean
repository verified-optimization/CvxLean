import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.ChangeOfVariables

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

instance : ChangeOfVariables (fun (xy : ℝ × ℝ) => (xy.1 + 1, xy.2)) := by 
  infer_instance

instance : ChangeOfVariables (fun (xy : ℝ × ℝ) => (Real.exp xy.1, xy.2)) := by 
  infer_instance

instance : ChangeOfVariables (fun (xy : ℝ × ℝ) => (xy.1 + 1, xy.2)) := by 
  infer_instance

end ChangeOfVariablesInstances

def p := 
  optimization (x y : ℝ)
    minimize (x + y)
    subject to 
      h : 0 < x

equivalence eqv/q1 : p := by 
  unfold p 
  change_of_variables (u) (x ↦ Real.exp u)
  equivalence_rfl

#print q1

equivalence eqv2/q2 : p := by 
  unfold p 
  change_of_variables (u) (y ↦ u + (1 : ℝ))
  equivalence_rfl

#print q2

equivalence eqv3/q3 : p := by 
  unfold p 
  change_of_variables (u) (x ↦ (1 : ℝ) / u)
  equivalence_rfl

#print q3