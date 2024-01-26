import CvxLean

noncomputable section

namespace FittingSphere

open CvxLean Minimization Real BigOperators Matrix

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
    . rintro _ h; exact le_trans (by norm_num) h
  rename_vars [c, t]
  -- Clean up.
  conv_constr h₁ => dsimp
  -- conv_constr h₂ => dsimp
  conv_obj => dsimp
  -- Rewrite objective.
  rw_obj =>
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
  -- equivalence_step =>
  --   apply Equivalence.rewrite_constraints
  --     (cs' := fun (ct : (Fin n → ℝ) × ℝ) => 0 ≤ ct.2 ∧ ‖ct.1‖ ^ 2 ≤ 50)
  --   . rintro ⟨c, t⟩; dsimp; constructor
  --     . rintro ⟨h₁, h₂⟩
  --       refine ⟨?_, h₂⟩
  --       rw [← neg_le_neg_iff] at h₂
  --       apply le_trans h₂
  --       rw [neg_le_iff_add_nonneg]
  --       apply le_of_lt
  --       rw [← sqrt_pos]
  --       exact lt_of_lt_of_le (by norm_num) h₁
  --     . rintro ⟨h₁, h₂⟩
  --       refine ⟨?_, h₂⟩
  --       have h_num : 1 / 10000 = sqrt ((1 / 10000) ^ 2) := by rw [rpow_two, sqrt_sq (by norm_num)]
  --       rw [h_num]
  --       apply sqrt_le_sqrt
  --       sorry

private lemma reduced_constraint (c : Fin n → ℝ) (t : ℝ) (h : 1 / 10000 ≤ t) :
    1 / 100 ≤ sqrt (t + ‖c‖ ^ 2) := by
  simp; rw [le_sqrt (by norm_num), ←add_zero (_ ^ 2)]
  . apply add_le_add _ (sq_nonneg _)
    exact le_trans (by norm_num) h
  . exact add_nonneg (le_trans (by norm_num) h) (sq_nonneg _)

#check le_sqrt_of_sq_le
#check le_sqrt'

def rrr : Reduction
    (optimization (c : Fin n → ℝ) (t : ℝ)
      minimize (Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2) : ℝ)
      subject to
        h₁ : 1 / 100 ≤ sqrt (t + ‖c‖ ^ 2)
        h₂ : ‖c‖ ^ 2 ≤ 50
    )
    (optimization (c : Fin n → ℝ) (t : ℝ)
      minimize (Vec.sum ((Vec.norm x ^ 2 - 2 * mulVec x c - Vec.const m t) ^ 2) : ℝ)
      subject to
        h₁ : 1 / 10000 ≤ t
        h₂ : ‖c‖ ^ 2 ≤ 50
    ) :=
  { psi := id,
    psi_feasibility := fun ⟨c, t⟩ ⟨h₁, h₂⟩ => ⟨reduced_constraint n c t h₁, h₂⟩,
    psi_optimality := fun ⟨c, t⟩ ⟨⟨h₁, h₂⟩, h_opt⟩ =>
      ⟨⟨reduced_constraint n c t h₁, h₂⟩, by
        rintro ⟨c', t'⟩ ⟨h₁', h₂'⟩
        simp [fittingSphere₁, feasible] at h₁ h₂ h₁' h₂' h_opt ⊢
        have ht' : 1 / 10000 ≤ t' := by
          simp
          rw [le_sqrt' (by norm_num)] at h₁'
          -- have : 0 < t' + ‖c'‖ ^ 2 := by
          --   by_contra hc
          --   simp [not_lt] at hc
          --   simp [sqrt_eq_zero_of_nonpos hc] at h₁'
          --   linarith [h₁']

          sorry
        simp at ht'
        exact h_opt c' t' ht' h₂'⟩  }

-- def fittingSphere₁InitialRed :
--     fittingSphere₁ n m x ≼
--     optimization (c : Fin n → ℝ) (t : ℝ)
--       minimize (∑ i, (‖(x i) - c‖ ^ 2 - sqrt (t + ‖c‖ ^ 2) ^ 2) ^ 2 : ℝ)
--       subject to
--         h : 1 / 10000 ≤ t :=
--   { psi := id,
--     psi_feasibility := fun ⟨c, t⟩ h => reduced_constraint n c t h
--     psi_optimality := fun ⟨c, t⟩ ⟨h_feas, h_opt⟩ =>
--       ⟨reduced_constraint n c t h_feas, by
--         rintro ⟨c', t'⟩ h_feas'
--         have h₁ := reduced_constraint n c t h_feas
--         simp [fittingSphere₁, feasible] at h₁ h_feas h_feas' h_opt ⊢
--         have ht' : 1 / 10000 ≤ t' := by
--           simp
--           apply le_trans h_feas'
--           sorry
--         simp at ht'
--         exact h_opt c' t' ht'
--         ⟩ }

-- reduction red/fittingSphere₂ (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere₁ n m x := by
--   reduction_step =>
--     sorry
--     -- apply Reduction.rewrite_objFun
--     --   (g := fun (ct : (Fin n → ℝ) × ℝ) =>
--     --     Vec.sum (((Vec.norm x) ^ 2 - 2 * (Matrix.mulVec x ct.1) - Vec.const m ct.2) ^ 2))
--     -- rintro ⟨c, t⟩ h
--     -- simp at h
--     -- simp [Vec.sum]
--     -- congr <;> ext i <;> congr 1
--     -- rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
--     -- simp [Vec.norm, Vec.const]

--     -- by_cases (0 < t + ‖c‖ ^ 2)

-- -- rw_obj =>
-- --   have h' : 0 < t + ‖c‖ ^ 2 := sqrt_pos.mp <| h;
-- --   conv =>
-- --     left; congr; congr; ext i; congr; simp;
-- --     rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
-- --     rw [sq_sqrt (rpow_two _ ▸ le_of_lt h')]
-- --     ring_nf; simp

#print eqv

end FittingSphere

end
