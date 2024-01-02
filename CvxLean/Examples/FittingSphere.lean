import CvxLean.Lib.Equivalence
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Tactic.ChangeOfVariables.ChangeOfVariables
import CvxLean.Command.Equivalence
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real BigOperators

lemma norm_sq {n : ℕ} (x : Fin n → ℝ) : ‖x‖ ^ (2 : ℝ) = x ⬝ᵥ x := by
  simp [Norm.norm, dotProduct]
  have h : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [sq_sqrt h]
  congr; funext i
  rw [pow_two]

lemma norm_diff_sq {n : ℕ} (x y : Fin n → ℝ) :
  ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (x ⬝ᵥ y) + ‖y‖ ^ 2 := by
  simp [Norm.norm, dotProduct]
  have h1 : 0 ≤ ∑ i, (x i - y i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h3 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [sq_sqrt h1, sq_sqrt h2, sq_sqrt h3]
  simp [sub_sq, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

namespace FittingSphere

noncomputable section

variable {n : ℕ} {m : ℕ} (x : Matrix (Fin m) (Fin n) ℝ)

def p :=
  optimization (c : Fin n → ℝ) (r : ℝ)
    minimize (∑ i, ((‖x i - c‖ ^ (2 : ℝ) - r ^ (2 : ℝ)) ^ (2 : ℝ)) : ℝ)
    subject to
      h1 : 10e-6 ≤ r

#check Matrix.transpose

equivalence ψ/q {n m : ℕ} (x : Matrix (Fin m) (Fin n) ℝ) : p x := by
  unfold p
  -- Change of variables by hand. It should be:
  -- * change_of_variables (t) (r ↦ sqrt (t + ‖c‖ ^ 2))
  apply Minimization.Equivalence.trans
  { let m : (Fin n → ℝ) × ℝ → ((Fin n → ℝ) × ℝ) :=
      fun d => (d.1, sqrt (d.2 + ‖d.1‖ ^ (2 : ℝ)))
    let cov : ChangeOfVariables m := {
      inv := fun d => (d.1, d.2 ^ 2 - ‖d.1‖ ^ 2)
      condition := fun d => 0 ≤ d.2
      property := by
        rintro ⟨c, r⟩ h
        simpa using (sqrt_sq h) }
    have h : ∀ (x : (Fin n → ℝ) × ℝ), 10e-6 ≤ x.2 → cov.condition x := by
      rintro ⟨c, r⟩ h1
      have : 0 ≤ r := by positivity
      simpa using this
    apply ChangeOfVariables.toEquivalence (c := m) (cov := cov) (h := h) }
  -- Clean up and change objective.
  -- NOTE: We have lost names here.
  apply Minimization.Equivalence.trans
  { -- TODO(RFM): conv_obj only works with Solution.
    -- More generally, build a wrapper so that tactics can work with both
    -- equivalence and reduction.
    let g : (Fin n → ℝ) × ℝ → ℝ := fun d =>
      ∑ i, (‖x i‖ ^ (2 : ℝ) - 2 * ((x i) ⬝ᵥ d.1) - d.2) ^ (2 : ℝ)
    apply MinimizationQ.rewrite_objective (g := g)
    { rintro ⟨c, t⟩ h1
      dsimp at h1
      simp at h1 ⊢; congr 1; funext i; congr 1;
      rw [norm_diff_sq (x i) c]
      have h1' : 0 < sqrt (t + ‖c‖ ^ 2) := by positivity
      rw [sqrt_pos] at h1'
      rw [sq_sqrt (le_of_lt h1')]
      ring } }
  -- Remove norms.
  dsimp; simp only [norm_sq]; norm_num_clean_up
  -- TODO(RFM): Make dcp tactic work in equivalence mode.
  -- Vector form for objective.
  apply Minimization.Equivalence.trans
  { let g : (Fin n → ℝ) × ℝ → ℝ := fun d =>
      (let y := (x * xᵀ - (2 : ℝ) • (Matrix.const m d.1) * xᵀ - Matrix.diagonal (Vec.const m d.2));
        (diag y) ⬝ᵥ (diag y))
    apply MinimizationQ.rewrite_objective (g := g)
    { rintro ⟨c, t⟩ _h1
      simp only [trace]
      congr 1; funext i;
      simp [pow_two]
      suffices hsuff : x i ⬝ᵥ x i - 2 * x i ⬝ᵥ c - t
        = (x * xᵀ) i i - ((2 : ℝ) • (const m c * xᵀ)) i i - Vec.const m t i
      { simp [hsuff] }
      simp [Vec.const, Matrix.const, Matrix.mul_apply']
      rw [dotProduct_comm] }
  }

reduction ψ'/r {n m : ℕ} (x : Fin m → Fin n → ℝ) : q x := by
  unfold q
  -- Finally:
  dcp -- fails because of diag * diag, we need an atom Vec.sqSum

end

end FittingSphere
