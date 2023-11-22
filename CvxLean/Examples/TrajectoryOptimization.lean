import CvxLean.Lib.Equivalence
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real

noncomputable section TrajectoryOptimization

open Matrix

def originalBezier (n d : ℕ)
  (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
  (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
  (A : Matrix (Fin d) (Fin n) ℝ)
  (k : Fin (d + 2) → ℝ)
  (v : Fin (d + 1) → ℝ)
  (a : Fin d → ℝ) :=
  optimization (x : Fin n → ℝ) (T : ℝ)
    minimize T
    subject to
      hT : 1 ≤ T
      hk : K.mulVec x ≤ k
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ T ^ 2 • a

def convexBezier (n d : ℕ)
  (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
  (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
  (A : Matrix (Fin d) (Fin n) ℝ)
  (k : Fin (d + 2) → ℝ)
  (v : Fin (d + 1) → ℝ)
  (a : Fin d → ℝ) :=
  optimization (x : Fin n → ℝ) (T : ℝ) (y : ℝ)
    minimize Real.sqrt (y - T)
    subject to
      hT : 1 ≤ T
      hk : K.mulVec x ≤ k
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ y • a
      hy : T ^ 2 ≤ y

variable {R D E : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R)

structure Relaxation :=
  (r : D → E)
  (r_injective : Function.Injective r)
  (r_feasibility : ∀ x, p.constraints x → q.constraints (r x))
  (r_lower_bound : ∀ x, p.constraints x → q.objFun (r x) ≤ p.objFun x)

-- def relaxationBezier (n d : ℕ)
--   (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
--   (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
--   (A : Matrix (Fin d) (Fin n) ℝ)
--   (k : Fin (d + 2) → ℝ)
--   (v : Fin (d + 1) → ℝ)
--   (a : Fin d → ℝ) :
--   Solution (convexBezier n d K V A k v a) → Solution (originalBezier n d K V A k v a) :=
--   fun ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy⟩, hopt⟩ => {
--     point := ⟨x, T⟩,
--     feasibility := ⟨hT, hk, hv, ha⟩,
--     optimality := sorry
--   }

-- def equiv (n d : ℕ)
--   (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
--   (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
--   (A : Matrix (Fin d) (Fin n) ℝ)
--   (k : Fin (d + 2) → ℝ)
--   (v : Fin (d + 1) → ℝ)
--   (a : Fin d → ℝ) :
--   Equivalence (originalBezier n d K V A k v a) (convexBezier n d K V A k v a) :=
--   { phi := fun ⟨⟨x, T⟩, ⟨hT, hk, hv, ha⟩⟩ =>
--       ⟨⟨x, T, T ^ 2⟩, ⟨hT, hk, hv, ha, le_refl _⟩⟩, --, by {
--       --   intros i hai
--       --   simp
--       -- }⟩⟩,
--     psi := fun ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy⟩⟩ =>
--       ⟨⟨x, T⟩, by {
--       simp at hT hk hv ha hy
--       have h0T : 0 ≤ T := by positivity
--       have h0T2 : 0 ≤ T ^ 2 := by positivity
--       have h0y : 0 ≤ y := le_trans h0T2 (rpow_two _ ▸ hy)
--       have hTsqrty := (le_sqrt h0T h0y).2 hy
--       refine' ⟨hT, hk, hv, _⟩
--       -- { exact le_trans hT hTsqrty }
--       -- { intros i
--       --   have hvi := hv i
--       --   simp at hvi ⊢
--       --   by_cases (v i < 0)
--       --   { have hfixi := hfix i h
--       --     exact le_trans hvi sorry }
--       --   { replace h := le_of_not_lt h
--       --     have hTvisqrtyvi := mul_le_mul_of_nonneg_right hTsqrty h
--       --     exact le_trans hvi hTvisqrtyvi } }
--       { intros i
--         have hai := ha i
--         simp at hai ⊢
--         by_cases (a i < 0)
--         { have hfixi := hfix i h
--           exact le_trans hai  (rpow_two _ ▸ hfixi) }
--         { replace h := le_of_not_lt h
--           have hT2aiyai := mul_le_mul_of_nonneg_right hy h
--           exact le_trans hai hT2aiyai } } }⟩,
--     phi_optimality := fun ⟨⟨x, T⟩, ⟨hT, hk, hv, ha⟩⟩ hopt
--       ⟨⟨x', T', y'⟩, ⟨hT', hk', hv', ha', hy', hfix'⟩⟩ => by {
--       simp at hT hk hv ha hT' hk' hv' ha' hy' hfix'
--       simp only [optimal, objFun, originalBezier, convexBezier] at hopt ⊢
--       have := hopt ⟨⟨x', sqrt y'⟩, by {
--         have h0T : 0 ≤ T' := by positivity
--         have h0T2 : 0 ≤ T' ^ 2 := by positivity
--         have h0y : 0 ≤ y' := le_trans h0T2 (rpow_two _ ▸ hy')
--         have hTsqrty := (le_sqrt h0T h0y).2 hy'
--         refine' ⟨_, hk', _, _⟩
--         { exact le_trans hT' hTsqrty }
--         { intros i
--           have hvi := hv' i
--           simp at hvi ⊢
--           by_cases (v i < 0)
--           { have hfixi := hfix' i h
--             exact le_trans hvi sorry }
--           { replace h := le_of_not_lt h
--             have hTvisqrtyvi := mul_le_mul_of_nonneg_right hTsqrty h
--             exact le_trans hvi hTvisqrtyvi } }
--         { simp [sq_sqrt h0y]
--           exact ha' } }⟩
--       simp at this
--       sorry -- I think I can prove this.
--     },
--     psi_optimality := fun ⟨⟨x, T, y⟩, ⟨hT, hk, hv, ha, hy, hfix⟩⟩ hopt
--       ⟨⟨x', T'⟩, ⟨hT', hk', hv', ha'⟩⟩ => by {
--       simp at hT hk hv ha hy hfix hT' hk' hv' ha'

--     }
--   }

end TrajectoryOptimization
