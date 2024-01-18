import CvxLean

open CvxLean Minimization Real

noncomputable section

namespace Chapter3

namespace CvxLean_overview

def p :=
  optimization (x y : ℝ)
    minimize 40 * x + 30 * y
    subject to
      c₁ : 12 ≤ x + y
      c₂ : 16 ≤ 2 * x + y

example : p =
    Minimization.mk
      (fun p => 40 * p.1 + 30 * p.2)
      (fun p => 12 ≤ p.1 + p.2 ∧ 16 ≤ 2 * p.1 + p.2) :=
  rfl

def pSolution : Solution p :=
  { point := ⟨4, 8⟩,
    isOptimal := by
      split_ands <;> try norm_num
      intros x' y' h_feas; simp [feasible, p] at h_feas ⊢; linarith }

end CvxLean_overview

namespace Equivalences

def p₁ := Minimization.mk (fun (x : ℝ) => x) (fun x => 1 ≤ x)
def p₂ := Minimization.mk (fun (x : ℝ) => log x) (fun x => 1 ≤ x)
def p₃ := Minimization.mk (fun (x : ℝ) => (log x) ^ (2 : ℝ)) (fun x => 1 ≤ x)

def E₁₂ : p₁ ≡ p₂ := Equivalence.map_objFun_log (fun x h => by positivity!)

def E₂₃ : p₂ ≡ p₃ := Equivalence.map_objFun_sq (fun x h => by positivity!)

def nS₁₂ : (p₁ ≡' p₂) → False :=
  fun ⟨_, psi, _, psi_feasibility, _, psi_optimality⟩ => by
    simp [p₁, p₂, feasible, constraints, objFun] at *
    let y : ℝ := 1
    have h_feas_y : 1 ≤ y := by norm_num
    have h_one_le_phiy := psi_feasibility y h_feas_y
    have h_psiy_le_logy := psi_optimality y h_feas_y
    have h_one_le_logy := le_trans h_one_le_phiy h_psiy_le_logy
    simp at h_one_le_logy
    have hc := lt_of_le_of_lt h_one_le_logy (zero_lt_one (α:= ℝ))
    exact lt_irrefl _ hc

end Equivalences

end Chapter3

end
