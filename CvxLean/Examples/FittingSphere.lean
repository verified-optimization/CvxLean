import CvxLean

noncomputable section

open CvxLean Minimization Real BigOperators Matrix

section LeastSquares

def leastSquares {n : ℕ} (a : Fin n → ℝ) :=
  optimization (x : ℝ)
    minimize (∑ i, ((a i - x) ^ 2) : ℝ)

@[reducible]
def mean {n : ℕ} (a : Fin n → ℝ) : ℝ := (1 / n) * ∑ i, (a i)

lemma leastSquares_alt_objFun {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ) :
  (∑ i, ((a i - x) ^ 2)) = n * ((x - mean a) ^ 2 + mean (a ^ 2) - (mean a) ^ 2) := by
  calc
  _ = ∑ i, ((a i) ^ 2 - 2 * (a i) * x + (x ^ 2)) := by congr; funext i; simp; ring
  _ = ∑ i, ((a i) ^ 2) - 2 * x * ∑ i, (a i) + n * (x ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    simp [Finset.sum_const]; ring
  _ = n * mean (a ^ 2) - 2 * x * n * mean a + n * (x ^ 2) := by
    simp [mean]; field_simp; ring
  _ = n * ((x - mean a) ^ 2 + mean (a ^ 2) - (mean a) ^ 2) := by
    simp [mean]; field_simp; ring

lemma leastSquares_optimal_eq_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ)
  (h : (leastSquares a).optimal x) : x = mean a := by
  simp [optimal, feasible, leastSquares] at h
  replace h : ∀ y,
    (x - mean a) ^ 2 + mean (a ^ 2) - (mean a) ^ 2 ≤
    (y - mean a) ^ 2 + mean (a ^ 2) - (mean a) ^ 2 := by
    intros y
    have hy := h y
    have h_rw_x := leastSquares_alt_objFun hn a x
    have h_rw_y := leastSquares_alt_objFun hn a y
    simp only [rpow_two] at h_rw_x h_rw_y ⊢
    rw [h_rw_x, h_rw_y] at hy
    rw [mul_le_mul_left (by positivity)] at hy
    exact hy
  replace h : ∀ y, (x - mean a) ^ 2 ≤ (y - mean a) ^ 2 := by
    intros y
    have hy := h y
    rw [← add_sub, ← add_sub, add_le_add_iff_right] at hy
    exact hy
  have hmean := h (mean a)
  simp at hmean
  have hz := le_antisymm hmean (sq_nonneg _)
  rwa [sq_eq_zero_iff, sub_eq_zero] at hz

def Vec.leastSquares {n : ℕ} (a : Fin n → ℝ) :=
  optimization (x : ℝ)
    minimize (Vec.sum ((a - Vec.const n x) ^ 2) : ℝ)

lemma vec_leastSquares_optimal_eq_mean {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (x : ℝ)
  (h : (Vec.leastSquares a).optimal x) : x = mean a := by
  apply leastSquares_optimal_eq_mean hn a
  simp [Vec.leastSquares, leastSquares, optimal, feasible] at h ⊢
  intros y
  simp only [Vec.sum, Pi.pow_apply, Pi.sub_apply, Vec.const] at h
  exact h y

lemma squared_error_eq_zero_iff {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    ∑ i, (a i - x) ^ 2 = 0 ↔ ∀ i, a i = x := by
  simp [rpow_two]
  constructor
  . intros h i
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h
    have hi := h i (by simp)
    rw [sq_eq_zero_iff, sub_eq_zero] at hi
    exact hi
  . intros h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
    intros i _
    simp [sq_eq_zero_iff, sub_eq_zero]
    exact h i

lemma vec_squared_norm_error_eq_zero_iff {n m : ℕ} (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i, ‖a i - x‖ ^ 2 = 0 ↔ ∀ i, a i = x := by
  simp [rpow_two]
  constructor
  . intros h i
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h
    have hi := h i (by simp)
    rw [sq_eq_zero_iff] at hi
    rw [@norm_eq_zero _ (PiLp.normedAddCommGroup _ _).toNormedAddGroup] at hi
    rw [sub_eq_zero] at hi
    exact hi
  . intros h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
    intros i _
    rw [sq_eq_zero_iff]
    rw [@norm_eq_zero _ (PiLp.normedAddCommGroup _ _).toNormedAddGroup]
    rw [sub_eq_zero]
    exact h i

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
      h₁ : 0 < r

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
    . rintro _ h; exact le_of_lt h
  rename_vars [c, t]
  -- Clean up.
  conv_constr h₁ => dsimp
  -- conv_constr h₂ => dsimp
  conv_obj => dsimp
  -- Rewrite objective.
  rw_obj =>
    -- NOTE: this is why we need strict postivity of `r`, to be able to apply `sq_sqrt`.
    have h' : 0 < t + ‖c‖ ^ 2 := sqrt_pos.mp <| h₁;
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

relaxation red/fittingSphere₂ (n m : ℕ) (x : Fin m → Fin n → ℝ) : fittingSphere₁ n m x := by
  relaxation_step =>
    apply Relaxation.weaken_constraint (cs' := fun _ => True)
    . rintro ⟨c, t⟩ _; trivial

-- This tells us that solving the relaxed problem is sufficient for optimal points if the solution
-- is non-trivial.
lemma optimal_relaxed_implies_optimal (hm : 0 < m) (c : Fin n → ℝ) (t : ℝ)
  (h_nontrivial : x ≠ Vec.const m c)
  (h : (fittingSphere₂ n m x).optimal (c, t)) : (fittingSphere₁ n m x).optimal (c, t) := by
  simp [fittingSphere₁, fittingSphere₂, optimal, feasible] at h ⊢
  constructor
  . let a := Vec.norm x ^ 2 - 2 * mulVec x c
    have h_ls : optimal (Vec.leastSquares a) t := by
      refine ⟨trivial, ?_⟩
      intros y _
      simp [objFun, Vec.leastSquares]
      exact h c y
    have ht_eq := vec_leastSquares_optimal_eq_mean hm a t h_ls
    have hc2_eq : ‖c‖ ^ 2 = (1 / m) * ∑ i : Fin m, ‖c‖ ^ 2 := by
      simp [Finset.sum_const]
      field_simp; ring
    have ht : t + ‖c‖ ^ 2 = (1 / m) * ∑ i, ‖(x i) - c‖ ^ 2 := by
      rw [ht_eq]; dsimp [mean]
      rw [hc2_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr; funext i;
      rw [← mul_add]
      congr; simp [Vec.norm]
      rw [@norm_sub_sq ℝ (Fin n → ℝ) _ (PiLp.normedAddCommGroup _ _) (PiLp.innerProductSpace _)]
      congr
    have h_tc2_nonneg : 0 ≤ t + ‖c‖ ^ 2 := by
      rw [ht]
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intros i _
      rw [rpow_two]
      exact sq_nonneg _
    cases (lt_or_eq_of_le h_tc2_nonneg) with
    | inl h_tc2_lt_zero =>
        convert h_tc2_lt_zero; simp
    | inr h_tc2_eq_zero =>
        exfalso
        rw [ht, zero_eq_mul] at h_tc2_eq_zero
        rcases h_tc2_eq_zero with (hc | h_sum_eq_zero)
        . simp at hc; linarith
        rw [vec_squared_norm_error_eq_zero_iff] at h_sum_eq_zero
        apply h_nontrivial
        funext i
        exact h_sum_eq_zero i
  . intros c' x' _
    exact h c' x'

#print fittingSphere₂

end FittingSphere

end
