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

namespace Relaxations

def p₁ :=
  optimization (x y : ℝ)
    minimize x + y
    subject to
      c₁ : 0 ≤ x
      c₂ : 0 ≤ y

def p₂ :=
  optimization (x : ℝ)
    minimize x
    subject to
      c₁ : 0 ≤ x

def Rx₁₂ : p₁ ≽' p₂ :=
  { phi := fun (x, _) => x,
    phi_feasibility := fun _ ⟨hx, _⟩ => hx,
    phi_optimality := fun _ ⟨_, hy⟩ => by simpa [objFun, p₁, p₂] }

open Real Matrix

lemma PosSemiDef_is_symmetric {n} {A : Matrix (Fin n) (Fin n) ℝ} (hA : PosSemidef A) :
  ∀ i j, A i j = A j i := by
  let h_A_IsHermitian := hA.1
  rw [Matrix.isHermitian_iff_isSymmetric] at h_A_IsHermitian
  simp [LinearMap.IsSymmetric, toEuclideanLin] at h_A_IsHermitian
  intros i j
  have hAij := h_A_IsHermitian (fun k => if k = i then 1 else 0) (fun k => if k = j then 1 else 0)
  have hi : (Finset.sum Finset.univ fun x => A j x * (Equiv.refl (WithLp 2 (Fin n → ℝ)))
    (fun k => if k = i then 1 else 0) x) = A j i := by simp
  have hj : (Finset.sum Finset.univ fun x => A i x * (Equiv.refl (WithLp 2 (Fin n → ℝ)))
    (fun k => if k = j then 1 else 0) x) = A i j := by simp
  simp [WithLp.equiv, mulVec, dotProduct] at hAij
  erw [hi, hj] at hAij
  rw [hAij]

lemma trace_mul_transpose_self_eq_quad_of_symm {n} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (h_A_symm : ∀ i j, A i j = A j i) :
    trace (A * (Vec.toMatrix x * (Vec.toMatrix x)ᵀ)) = vecMul x A ⬝ᵥ x := by
  simp [trace, dotProduct]
  congr; funext i;
  simp [Matrix.mul_apply, vecMul, dotProduct, Finset.sum_mul]
  congr; funext j;
  simp [Vec.toMatrix]
  rw [h_A_symm i j]
  ring

def sdr {n} {A C : Matrix (Fin n) (Fin n) ℝ} (hA : PosSemidef A) (hC : PosSemidef C) (b : ℝ) :
  (optimization (x : Fin n → ℝ)
    minimize (vecMul x C) ⬝ᵥ x
    subject to
      c₁ : (vecMul x A) ⬝ᵥ x ≥ b) ≽'
  (optimization (X : Matrix (Fin n) (Fin n) ℝ)
    minimize trace (C * X)
    subject to
      c₁ : trace (A * X) ≥ b
      c₂ : PosSemidef X) :=
  { phi := fun x => (Vec.toMatrix x) * (Vec.toMatrix x)ᵀ,
    phi_feasibility := fun x h_feas_x => by
      simp [objFun, feasible, constraints, p₁, p₂, Vec.toMatrix] at *
      have h_A_symm := PosSemiDef_is_symmetric hA
      rw [trace_mul_transpose_self_eq_quad_of_symm A x h_A_symm]
      refine ⟨h_feas_x, ?_⟩
      rw [← conjTranspose_eq_transpose]
      exact posSemidef_conjTranspose_mul_self _,
    phi_optimality := fun x h_feas_x => by
      simp [objFun, feasible, constraints, p₁, p₂] at *
      have h_C_symm := PosSemiDef_is_symmetric hC
      rw [trace_mul_transpose_self_eq_quad_of_symm C x h_C_symm] }


end Relaxations

end Chapter3

end
