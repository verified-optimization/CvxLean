import Lean
import CvxLean.Lib.Minimization
import CvxLean.Lib.Equivalence
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Tactic.DCP.AtomLibrary

namespace CvxLean

open Minimization

class ChangeOfVariables {D E} (c : E → D) where 
  inv : D → E
  condition : D → Prop 
  property : ∀ x, condition x → c (inv x) = x

def ChangeOfVariables.toEquivalence {D E R} [Preorder R] 
  {f : D → R} {cs : D → Prop}
  (c : E → D) [cov : ChangeOfVariables c]
  (h : ∀ x, cs x → cov.condition x) :
  Equivalence 
    (Minimization.mk f cs)
    (Minimization.mk (fun x => f (c x)) (fun x => cs (c x))) := 
  StrongEquivalence.toEquivalence <| {
    phi := fun x => cov.inv x
    psi := fun y => c y
    phi_feasibility := fun x hx => by simp [cov.property x (h x hx)]; exact hx
    phi_optimality := fun x hx => by simp [cov.property x (h x hx)]
    psi_feasibility := fun y hy => hy
    psi_optimality := fun y _ => by simp
  }

instance ChangeOfVariables.comp {D E F} (c₁ : E → D) (c₂ : F → E) 
  [cov₁ : ChangeOfVariables c₁] [cov₂ : ChangeOfVariables c₂] 
  : ChangeOfVariables (c₁ ∘ c₂) := {
    inv := cov₂.inv ∘ cov₁.inv
    condition := fun x => cov₁.condition x ∧ cov₂.condition (cov₁.inv x)
    property := fun x ⟨hx₁, hx₂⟩ => by {
      simp [cov₂.property (cov₁.inv x) hx₂]
      simp [cov₁.property x hx₁]
    }
  } 

noncomputable section Instances

instance : ChangeOfVariables Real.exp := {
  inv := Real.log
  condition := fun x => 0 < x
  property := fun _ hx => Real.exp_log hx
} 

-- NOTE(RFM): x ≠ 0 is technically not necessary as division is defined on all 
-- of ℝ, but we want to avoid division by zero.  
instance : ChangeOfVariables (fun x : ℝ => x⁻¹) := {
  inv := fun x => x⁻¹
  condition := fun x => x ≠ 0 
  property := fun x _ => by field_simp
}

instance {a : ℝ} [i : Fact (a ≠ 0)] : ChangeOfVariables (fun x : ℝ => a * x) := {
  inv := fun x => (1 / a) * x
  condition := fun _ => True
  property := fun _ _ => by rw [← mul_assoc, mul_one_div, div_self i.out, one_mul]
}

instance {a : ℝ} [Fact (a ≠ 0)] : ChangeOfVariables (fun x : ℝ => a / x) := by 
  have := ChangeOfVariables.comp (fun x : ℝ => a * x) (fun x : ℝ => x⁻¹)
  simp only [Function.comp, mul_one_div, ←div_eq_mul_inv] at this 
  exact this

instance {a : ℝ} : ChangeOfVariables (fun x : ℝ => x + a) := {
  inv := fun x => x - a
  condition := fun _ => True
  property := fun _ _ => by ring
}

end Instances

/-
The idea here is to have a tactic

  change_of_variables (x ↦ e^u)

1. Detect exactly where to apply the change of variables. 
2. Syntesize the instance.
2. Prove the conditions. 
3. Apply the c-of-v to equivalence theorem.
-/

end CvxLean
