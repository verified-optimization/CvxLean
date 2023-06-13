import CvxLean.Command.Reduction
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real

noncomputable section TrajectoryOptimization

def problem1 (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin n) → ℝ) :=
  optimization (x : Fin m → ℝ) (T : ℝ) 
    minimize T 
    subject to 
      hT : 1 ≤ T -- 0 < T but can be rescaled?
      hk : K.mulVec x ≤ k 
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ T ^ 2 • a

def problem2 (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin n) → ℝ) :=
  optimization (x : Fin m → ℝ) (T : ℝ) (y : ℝ) 
    minimize y - T 
    subject to 
      hT : 1 ≤ T
      hk : K.mulVec x ≤ k 
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ y • a
      hy : T ^ 2 ≤ y

section Counterexample

def K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -1
def V : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -1
def A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
def k : (Fin 1) → ℝ := fun _ => -1
def v : (Fin 1) → ℝ := fun _ => -2
def a : (Fin 1) → ℝ := fun _ => 1

def sol1 : Solution (problem1 K V A k v a) := 
  { point := ⟨4, 2⟩,
    feasibility := by 
      simp [K, V, A, k, v, a, problem1]
      simp [mulVec, dotProduct, Pi.hasLe, constraints, OfNat.ofNat]
      norm_num,
    optimality := by 
      rintro ⟨⟨x, T⟩, hc⟩
      simp [K, V, A, k, v, a, problem1] at hc ⊢
      simp [mulVec, dotProduct, Pi.hasLe, constraints, objFun] at hc ⊢
      rcases hc with ⟨hT, hk, hv, ha⟩
      have h := le_trans hv ha 
      rw [pow_two] at h
      exact le_of_mul_le_mul_left h (lt_of_lt_of_le zero_lt_one hT)
  }

def sol2 : Solution (problem2 K V A k v a) := 
  { point := ⟨2, 1, 2⟩,
    feasibility := by 
      simp [K, V, A, k, v, a, problem2]
      simp [mulVec, dotProduct, Pi.hasLe, constraints, OfNat.ofNat]
      norm_num,
    optimality := by 
      rintro ⟨⟨x, T, y⟩, hc⟩
      simp [K, V, A, k, v, a, problem2] at hc ⊢
      simp [mulVec, dotProduct, Pi.hasLe, constraints, objFun] at hc ⊢
      rcases hc with ⟨hT, hk, hv, ha, hy⟩
      linarith
  }

end Counterexample

section Relaxation

/-- We say that p is a realaxation of q if there is an embedding from the 
feasible set of q to the feasible set of p. -/
structure Relaxation {R D E : Type} [Preorder R] 
  (p : Minimization D R) (q : Minimization E R) where 
  f : E ↪ D
  feasibility : ∀ y, q.constraints y → p.constraints (f y)

notation p " ⊇ᵣ " q => Relaxation p q

-- NOTE(RFM): problem2 is a relaxation of problem1.
def relaxation12 (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin n) → ℝ) :
  (problem2 K V A k v a) ⊇ᵣ (problem1 K V A k v a) := 
  { f := ⟨
      fun ⟨x, T⟩ => ⟨x, T, T ^ 2⟩, 
      fun ⟨x₁, T₁⟩ ⟨x₂, T₂⟩ h => by simp at h ⊢; exact ⟨h.1, h.2.1⟩ ⟩,
    feasibility := fun _ ⟨hT, hk, hv, ha⟩ => ⟨hT, hk, hv, ha, le_refl _⟩ 
  }

-- TODO(RFM): Move.
lemma smul_le_of_le_of_nonneg 
  {a b : ℝ} (hab : a ≤ b) {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) :
  a • v ≤ b • v := fun i =>
  mul_le_mul_of_nonneg_right hab (hv i)

-- NOTE(RFM): problem2 is a tight relaxation of problem1 if v is nonnegative. 
-- Note that this only makes sense together with the map that induces the solution 
-- map, in this case (x, T) ↦ (x, T, T ^ 2).
-- TODO(RFM): Package it as definition.
lemma relaxation12_tight (K V A : Matrix (Fin n) (Fin m) ℝ) 
  (k v a : (Fin n) → ℝ) (hvnn : ∀ i, 0 ≤ v i) : 
  Solution (problem1 K V A k v a) → Solution (problem2 K V A k v a) := 
  fun ⟨⟨xopt, Topt⟩, ⟨hTopt, hkopt, hvopt, haopt⟩, hoptimality⟩ => {
    point := ⟨xopt, Topt, Topt ^ 2⟩,
    feasibility := ⟨hTopt, hkopt, hvopt, haopt, le_refl _⟩,
    optimality := fun ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy⟩⟩ => by 
      simp at hTopt hkopt hvopt haopt hT hk hv ha hy
      simp only [problem1, problem2, objFun, constraints] at hoptimality ⊢
      have hToptnn := le_trans zero_le_one hTopt
      have hToptsub1nn := sub_nonneg_of_le hTopt
      have hTnn := le_trans zero_le_one hT
      have hT2nn := pow_nonneg hTnn 2
      have h1leT2 := pow_le_pow_of_le_left zero_le_one hT 2
      simp only [one_pow] at h1leT2
      have hynn := le_trans hT2nn hy
      have h1ley := le_trans h1leT2 hy
      have h1lesqrty := sqrt_le_sqrt h1ley 
      simp only [sqrt_one] at h1lesqrty
      have hTlesqrty := (le_sqrt hTnn hynn).2 hy
      have hTvlesqrtyv : T • v ≤ sqrt y • v := 
        smul_le_of_le_of_nonneg hTlesqrty hvnn
      have hVxlesqrtyv := le_trans hv hTvlesqrtyv
      have hAxlesqrty2v : A.mulVec x ≤ (sqrt y) ^ 2 • a := by 
        rw [rpow_two, sq_sqrt hynn]
        exact ha
      have hToptlesqrty := 
        hoptimality ⟨⟨x, sqrt y⟩, ⟨h1lesqrty, hk, hVxlesqrtyv, hAxlesqrty2v⟩⟩
      simp at hToptlesqrty
      have hTopt2ley : Topt ^ 2 ≤ y := 
        rpow_two _ ▸ (le_sqrt hToptnn hynn).1 hToptlesqrty
      rcases (lt_trichotomy T Topt) with (hTltTopt | hTeqTopt | hToptltT)
      { exact sub_le_sub (rpow_two Topt ▸ hTopt2ley) (le_of_lt hTltTopt) }
      { rw [hTeqTopt] at hy ⊢
        simp [hy] }
      { have hToptleT := le_of_lt hToptltT
        have hT2subTleysubT : T ^ 2 - T ≤ y - T := 
          sub_le_sub (rpow_two _ ▸ hy) (le_refl _)
        have hTopt2subToptleT2subT : Topt ^ 2 - Topt ≤ T ^ 2 - T := by 
          have hToptsub1leTsub1 := sub_le_sub hToptleT (le_refl 1)
          have hintermediate : Topt * Topt - Topt * 1 ≤ T * T - T * 1 := by 
            rw [←mul_sub, ←mul_sub]
            apply mul_le_mul hToptleT hToptsub1leTsub1 hToptsub1nn hTnn
          rw [rpow_two, rpow_two, pow_two, pow_two]
          simp only [mul_one] at hintermediate
          exact hintermediate
        exact le_trans hTopt2subToptleT2subT hT2subTleysubT } } 

-- NOTE(RFM): In fact, we can show that every solution of problem2 satisfies the 
-- condition y = T ^ 2 provided that the vector v is nonnegative.
lemma relaxation12_tight' (K V A : Matrix (Fin n) (Fin m) ℝ) 
  (k v a : (Fin n) → ℝ) (hvnn : ∀ i, 0 ≤ v i) : 
  ∀ s : Solution (problem2 K V A k v a), s.point.2.2 = s.point.2.1 ^ 2 := by
  rintro ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy⟩, hoptimality⟩
  simp at hT hk hv ha hy
  simp only [problem2, objFun, constraints] at hoptimality ⊢;
  suffices y ≤ T ^ 2 by exact le_antisymm this (rpow_two _ ▸ hy)
  -- NOTE(RFM): Up to line 167 is taken from the previous proof.
  have hTnn := le_trans zero_le_one hT
  have hT2nn := pow_nonneg hTnn 2
  have h1leT2 := pow_le_pow_of_le_left zero_le_one hT 2
  simp only [one_pow] at h1leT2
  have hynn := le_trans hT2nn hy
  have h1ley := le_trans h1leT2 hy
  have h1lesqrty := sqrt_le_sqrt h1ley 
  simp only [sqrt_one] at h1lesqrty
  have hTlesqrty := (le_sqrt hTnn hynn).2 hy
  have hTvlesqrtyv : T • v ≤ sqrt y • v := 
    smul_le_of_le_of_nonneg hTlesqrty hvnn
  have hVxlesqrtyv := le_trans hv hTvlesqrtyv
  have hsqrty2ley := le_of_eq (sq_sqrt hynn)
  rw [←rpow_two] at hsqrty2ley
  have hsqrtyleT := 
      hoptimality ⟨⟨x, sqrt y, y⟩, ⟨h1lesqrty, hk, hVxlesqrtyv, ha, hsqrty2ley⟩⟩
  simp at hsqrtyleT
  rw [sub_add, sub_eq_add_neg, le_add_iff_nonneg_right] at hsqrtyleT
  rw [neg_nonneg, sub_nonpos] at hsqrtyleT
  exact rpow_two _ ▸ (sqrt_le_iff.1 hsqrtyleT).2

end Relaxation

end TrajectoryOptimization
