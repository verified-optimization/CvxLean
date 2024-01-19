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

def pex₁ := Minimization.mk (fun (x : ℝ) => x) (fun x => 1 ≤ x)
def pex₂ := Minimization.mk (fun (x : ℝ) => log x) (fun x => 1 ≤ x)
def pex₃ := Minimization.mk (fun (x : ℝ) => (log x) ^ (2 : ℝ)) (fun x => 1 ≤ x)

def E₁₂ : pex₁ ≡ pex₂ := Equivalence.map_objFun_log (fun x h => by positivity!)

def E₂₃ : pex₂ ≡ pex₃ := Equivalence.map_objFun_sq (fun x h => by positivity!)

def nS₁₂ : (pex₁ ≡' pex₂) → False :=
  fun ⟨_, psi, _, psi_feasibility, _, psi_optimality⟩ => by
    simp [pex₁, pex₂, feasible, constraints, objFun] at *
    let y : ℝ := 1
    have h_feas_y : 1 ≤ y := by norm_num
    have h_one_le_phiy := psi_feasibility y h_feas_y
    have h_psiy_le_logy := psi_optimality y h_feas_y
    have h_one_le_logy := le_trans h_one_le_phiy h_psiy_le_logy
    simp at h_one_le_logy
    have hc := lt_of_le_of_lt h_one_le_logy (zero_lt_one (α:= ℝ))
    exact lt_irrefl _ hc

def S₂₃ : pex₂ ≡' pex₃ :=
  { phi := fun x => (exp (sqrt (log x)))
    psi := fun x => (exp ((log x) ^ 2))
    phi_feasibility := fun x _ => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at *
      exact sqrt_nonneg _,
    psi_feasibility := fun x h_feas_x => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at *
      exact sq_nonneg _,
    phi_optimality := fun x h_feas_x => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at *
      have h_logx_nonneg : 0 ≤ log x := log_nonneg h_feas_x
      rw [sq_sqrt h_logx_nonneg],
    psi_optimality := fun x _ => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at * }

def p₄ := Minimization.mk (fun (x : ℝ) => x) (fun x => 0 ≤ x)

def S₄₂ : p₄ ≡' pex₂ :=
  { phi := fun x => exp x
    psi := fun x => log x
    phi_feasibility := fun x _ => by
      simp [p₄, pex₂, feasible, constraints, objFun] at *
      positivity!,
    psi_feasibility := fun x h_feas_x => by
      simp [p₄, pex₂, feasible, constraints, objFun] at *
      positivity!,
    phi_optimality := fun x _ => by
      simp [p₄, pex₂, feasible, constraints, objFun] at *,
    psi_optimality := fun x _ => by
      simp [p₄, pex₂, feasible, constraints, objFun] at *, }

def nS₄₁ : (p₄ ≡' pex₁) → False := fun h => nS₁₂ <| h.symm.trans S₄₂

equivalence eqv₁/p₂ :
    optimization (x y : ℝ)
      minimize (x * y)
      subject to
        c₁ : 0 < x
        c₂ : 1 ≤ y := by
  change_of_variables! (u) (x ↦ exp u)
  change_of_variables! (v) (y ↦ exp v)

equivalence eqv₂/p₃ : p₂ := by
  conv_obj =>
    rw [← exp_add]
  conv_constr c₂ =>
    rw [← log_le_log (by norm_num) (exp_pos _), log_exp]
    norm_num

open Equivalence

set_option trace.Meta.debug true

equivalence eqv/q :
    optimization (x : ℝ)
      minimize sqrt (x ^ 2)
      subject to
        c₁ : 0 ≤ x := by
  rw_obj =>
    rw [sqrt_sq c₁]

end Equivalences

end Chapter3

end
