import CvxLean

noncomputable section

open CvxLean Minimization Real BigOperators Matrix

section LeastSquares

def leastSquares {n : ℕ} (a : Fin n → ℝ) (lb : ℝ) :=
  optimization (x : ℝ)
    minimize (∑ i, ((a i - x) ^ 2) : ℝ)
    subject to
      h₁ : lb ≤ x

lemma leastSquares_optimal_eq_mean {n : ℕ} (a : Fin n → ℝ) (lb : ℝ) (x : ℝ)
  (h : (leastSquares a lb).optimal x) : x = (1 / n) * ∑ i, (a i) := by
  simp [leastSquares]
  sorry

def Vec.leastSquares {n : ℕ} (a : Fin n → ℝ) (lb : ℝ) :=
  optimization (x : ℝ)
    minimize (Vec.sum ((a - Vec.const n x) ^ 2) : ℝ)
    subject to
      h₁ : lb ≤ x

lemma vec_leastSquares_optimal_eq_mean {n : ℕ} (a : Fin n → ℝ) (lb : ℝ) (x : ℝ)
  (h : (Vec.leastSquares a lb).optimal x) : x = (1 / n) * ∑ i, (a i) := by
  apply leastSquares_optimal_eq_mean a lb
  simp [Vec.leastSquares, leastSquares, optimal, feasible] at h ⊢
  have ⟨h, h_opt⟩ := h
  refine ⟨h, ?_⟩
  intros y
  simp only [Vec.sum, Pi.pow_apply, Pi.sub_apply, Vec.const] at h_opt
  exact h_opt y

  -- if x is optimal then avg(x) = 1
  -- https://math.stackexchange.com/questions/2554243/understanding-the-mean-minimizes-the-mean-squared-error

end LeastSquares

namespace FittingSphere

-- Dimension.
variable (n : ℕ)

-- Number of points.
variable (m : ℕ)

-- Given points.
variable (x : Fin m → Fin n → ℝ)

def fittingSphere :=
  optimization (c : Fin n → ℝ) (r : ℝ)
    minimize (∑ i, (‖(x i) - c‖ ^ 2 - r ^ 2) ^ 2 : ℝ)
    subject to
      h₁ : 1 / 10000 ≤ r
      h₂ : ‖c‖ ^ 2 ≤ 50

instance : ChangeOfVariables fun (ct : (Fin n → ℝ) × ℝ) => (ct.1, sqrt (ct.2 + ‖ct.1‖ ^ 2)) :=
  { inv := fun (c, r) => (c, r ^ 2 - ‖c‖ ^ 2),
    condition := fun (_, t) => 0 ≤ t,
    property := fun ⟨c, t⟩ h => by simp [sqrt_sq h] }

def Vec.norm {m n} (x : Fin m → Fin n → ℝ) : Fin m → ℝ := fun i => ‖x i‖

equivalence eqv/fittingSphere₁ (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere n m x := by
  -- Change of variables.
  equivalence_step =>
    apply ChangeOfVariables.toEquivalence
      (fun (ct : (Fin n → ℝ) × ℝ) => (ct.1, sqrt (ct.2 + ‖ct.1‖ ^ 2)))
    . rintro _ ⟨h, _⟩; exact le_trans (by norm_num) h
  rename_vars [c, t]
  -- Clean up.
  conv_constr h₁ => dsimp
  -- conv_constr h₂ => dsimp
  conv_obj => dsimp
  -- Rewrite objective.
  rw_obj =>
    -- NOTE: this is why we need strict postivity of `r`, to be able to apply `sq_sqrt`.
    have h' : 0 < t + ‖c‖ ^ 2 := sqrt_pos.mp <| lt_of_lt_of_le (by norm_num) h₁;
    conv =>
      left; congr; congr; ext i; congr; simp;
      rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
      rw [sq_sqrt (rpow_two _ ▸ le_of_lt h')]
      ring_nf; simp
  equivalence_step =>
    apply Equivalence.rewrite_objFun
      (g := fun (ct : (Fin n → ℝ) × ℝ) =>
        Vec.sum (((Vec.norm x) ^ 2 - 2 * (Matrix.mulVec x ct.1) - Vec.const m ct.2) ^ 2))
    . rintro ⟨c, t⟩ h
      dsimp at h ⊢; simp [Vec.sum, Vec.norm, Vec.const]
      congr; funext i; congr 1; rw [add_sub, ← sub_eq_add_neg]
      congr 2; simp [mulVec, inner, dotProduct, Finset.sum_mul, Finset.mul_sum]
      congr; funext j; ring
  rename_vars [c, t]

#print fittingSphere₁

private lemma nonconvex__implies_relaxed_constraint (c : Fin n → ℝ) (t : ℝ)
    (h₁ : 1 / 10000 ≤ sqrt (t + ‖c‖ ^ 2)) (h₂ : ‖c‖ ^ 2 ≤ 50) : -50 ≤ t := by
  rw [le_sqrt' (by norm_num)] at h₁
  linarith

relaxation red/fittingSphere₂ (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere₁ n m x := by
  relaxation_step =>
    apply Relaxation.weaken_constraint (cs' := fun ct => -50 ≤ ct.2 ∧ ‖ct.1‖ ^ 2 ≤ 50)
    . rintro ⟨c, t⟩ ⟨h₁, h₂⟩
      exact ⟨nonconvex__implies_relaxed_constraint n c t h₁ h₂, h₂⟩

lemma optimal_relaxed_implies_optimal (hm : 0 < m) (c : Fin n → ℝ) (t : ℝ)
  (h : (fittingSphere₂ n m x).optimal (c, t)) : (fittingSphere₁ n m x).optimal (c, t) := by
  simp [fittingSphere₁, fittingSphere₂, optimal, feasible] at h ⊢
  have ⟨⟨h₁, h₂⟩, h_opt⟩ := h
  constructor
  . constructor
    . let a := Vec.norm x ^ 2 - 2 * mulVec x c
      have h_ls : optimal (Vec.leastSquares a (-50)) t := by
        refine ⟨h₁, ?_⟩
        intros y hy
        simp [objFun, Vec.leastSquares]
        exact h_opt c y hy h₂
      have ht_eq := vec_leastSquares_optimal_eq_mean a (-50) t h_ls
      have hc2_eq : ‖c‖ ^ 2 = (1 / m) * ∑ i : Fin m, ‖c‖ ^ 2 := by
        simp [Finset.sum_const]
        field_simp; ring
      have ht : t + ‖c‖ ^ 2 = (1 / m) * ∑ i, ‖(x i) - c‖ ^ 2 := by
        rw [ht_eq]; dsimp
        rw [hc2_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        congr; funext i;
        rw [← mul_add]
        congr; simp [Vec.norm]
        rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
        congr
      
      sorry
    . exact h₂
  . intros c' x' h₁' h₂'
    sorry

end FittingSphere

end
