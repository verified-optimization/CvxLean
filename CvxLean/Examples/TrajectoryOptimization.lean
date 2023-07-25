import CvxLean.Command.Reduction
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real

noncomputable section TrajectoryOptimization

open Matrix

def original (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin n) → ℝ) :=
  optimization (x : Fin m → ℝ) (T : ℝ) 
    minimize T 
    subject to 
      hT : 1 ≤ T -- 0 < T but can be rescaled?
      hk : K.mulVec x ≤ k 
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ T ^ 2 • a

def relaxed (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin n) → ℝ) :=
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

def originalSol : Solution (original K V A k v a) := 
  { point := ⟨4, 2⟩,
    feasibility := by 
      simp [K, V, A, k, v, a, original]
      simp [mulVec, dotProduct, Pi.hasLe, constraints, OfNat.ofNat]
      norm_num,
    optimality := by 
      rintro ⟨⟨x, T⟩, hc⟩
      simp [K, V, A, k, v, a, original] at hc ⊢
      simp [mulVec, dotProduct, Pi.hasLe, constraints, objFun] at hc ⊢
      rcases hc with ⟨hT, hk, hv, ha⟩
      have h := le_trans hv ha 
      rw [pow_two] at h
      exact le_of_mul_le_mul_left h (lt_of_lt_of_le zero_lt_one hT)
  }

def relaxedSol : Solution (relaxed K V A k v a) := 
  { point := ⟨2, 1, 2⟩,
    feasibility := by 
      simp [K, V, A, k, v, a, relaxed]
      simp [mulVec, dotProduct, Pi.hasLe, constraints, OfNat.ofNat]
      norm_num,
    optimality := by 
      rintro ⟨⟨x, T, y⟩, hc⟩
      simp [K, V, A, k, v, a, relaxed] at hc ⊢
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
def relaxation (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin n) → ℝ) :
  (relaxed K V A k v a) ⊇ᵣ (original K V A k v a) := 
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
def relaxationTight (K V A : Matrix (Fin n) (Fin m) ℝ) 
  (k v a : (Fin n) → ℝ) (hvnn : ∀ i, 0 ≤ v i) : 
  Solution (original K V A k v a) → Solution (relaxed K V A k v a) := 
  fun ⟨⟨xopt, Topt⟩, ⟨hTopt, hkopt, hvopt, haopt⟩, hoptimality⟩ => {
    point := ⟨xopt, Topt, Topt ^ 2⟩,
    feasibility := ⟨hTopt, hkopt, hvopt, haopt, le_refl _⟩,
    optimality := fun ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy⟩⟩ => by 
      simp at hTopt hkopt hvopt haopt hT hk hv ha hy
      simp only [original, relaxed, objFun, constraints] at hoptimality ⊢
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
        exact le_trans hTopt2subToptleT2subT hT2subTleysubT } 
      } 

-- NOTE(RFM): In fact, we can show that every solution of problem2 satisfies the 
-- condition y = T ^ 2 provided that the vector v is nonnegative.
def relaxation_tight' (K V A : Matrix (Fin n) (Fin m) ℝ) 
  (k v a : (Fin n) → ℝ) (hvnn : ∀ i, 0 ≤ v i) : 
  ∀ s : Solution (relaxed K V A k v a), s.point.2.2 = s.point.2.1 ^ 2 := by
  rintro ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy⟩, hoptimality⟩
  simp at hT hk hv ha hy
  simp only [relaxed, objFun, constraints] at hoptimality ⊢;
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

def originalBezier (K V A : ℝ) (k v a : ℝ) :=
  optimization (x0 x1 x2 : ℝ) (T : ℝ) 
    minimize T 
    subject to 
      hT : 1 ≤ T 
      hk0 : K * x0 ≤ k 
      hk1 : K * x1 ≤ k
      hk2 : K * x2 ≤ k
      hv1 : 2 * V * (x1 - x0) ≤ T * v
      hv2 : 2 * V * (x2 - x1) ≤ T * v
      ha : 2 * A * (x2 - 2 * x1 + x0) ≤ T ^ 2 * a

def relaxedBezier (K V A : ℝ) (k v a : ℝ) :=
  optimization (x0 x1 x2 : ℝ) (T : ℝ) (y : ℝ) 
    minimize y - T 
    subject to 
      hT : 1 ≤ T 
      hk0 : K * x0 ≤ k 
      hk1 : K * x1 ≤ k
      hk2 : K * x2 ≤ k
      hv10 : 2 * V * (x1 - x0) ≤ T * v
      hv21 : 2 * V * (x2 - x1) ≤ T * v
      ha : 2 * A * (x2 - 2 * x1 + x0) ≤ y * a
      hy : T ^ 2 ≤ y

#check Lean.MetaM

def relaxationBezierTight (K V A : ℝ) (k v a : ℝ)  : 
  Solution (originalBezier K V A k v a) → Solution (relaxedBezier K V A k v a) := 
  fun ⟨⟨x0opt, x1opt, x2opt, Topt⟩, 
       ⟨hTopt, hk0opt, hk1opt, hk2opt, hv1opt, hv2opt, haopt⟩, hoptimality⟩ => {
    point := ⟨x0opt, x1opt, x2opt, Topt, Topt ^ 2⟩,
    feasibility := ⟨hTopt, hk0opt, hk1opt, hk2opt, hv1opt, hv2opt, haopt, le_refl _⟩,
    optimality := fun ⟨⟨x0, x1, x2, T, y⟩, ⟨hT, hk0, hk1, hk2, hv1, hv2, ha, hy⟩⟩ => by {
      simp at hT hk0 hk1 hk2 hv1 hv2 ha hy
      simp only [originalBezier, relaxedBezier, objFun, constraints] at hoptimality ⊢;
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
      have ha' : 2 * A * (x2 - 2 * x1 + x0) ≤ (sqrt y) ^ 2 * a := by 
        rw [rpow_two, sq_sqrt hynn]
        exact ha


      have h1 : 2 * V * (x0 - x0) ≤ T * v := sorry
      have h := 
        hoptimality ⟨
          ⟨x0, x1, x2, T⟩, 
          ⟨sorry, sorry, sorry, sorry, sorry, sorry, sorry⟩⟩
      simp at h
      have hv : 
          2 * V * (x1 - x0) ≤ (sqrt y) * v 
        ∧ 2 * V * (x2 - x1) ≤ (sqrt y) * v := by {
          by_cases h : 0 ≤ v
          { -- This is trivial
            sorry }
          { have h := le_of_not_le h
            by_contra hc
            simp only [not_and_or, not_le] at hc
            have hvT := mul_nonpos_of_nonneg_of_nonpos hTnn h
            have hv1' := le_trans hv1 hvT
            have hv2' := le_trans hv2 hvT
            simp [mul_sub] at hv1' hv2'
            rcases hc with (hc1 | hc2)
            { have := lt_of_lt_of_le hc1 hv1
              -- simp [mul_sub] at hv1 hv2
              have : 2 * V * x2 - 2 * V * x1 - 2 * V * x0 ≤ 2 * T * v := by 
                have := add_le_add hv1 hv2
                have := add_le_add this hv1
                have := add_le_add this hv2
                ring_nf at this
                sorry
              
              sorry }
            { sorry } 
          }
      }
      have hToptlesqrty := 
        hoptimality ⟨
          ⟨x0, x1, x2, sqrt y⟩, 
          ⟨h1lesqrty, hk0, hk1, hk2, hv.1, hv.2, ha'⟩⟩
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
        exact le_trans hTopt2subToptleT2subT hT2subTleysubT } 
    } 
  }

end TrajectoryOptimization
