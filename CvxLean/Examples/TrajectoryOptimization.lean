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
    minimize y - T
    subject to
      hT : 1 ≤ T
      hk : K.mulVec x ≤ k
      hv : V.mulVec x ≤ T • v
      ha : A.mulVec x ≤ y • a
      hy : T ^ 2 ≤ y

-- map from cvx to og

-- are k, v and a constant?
theorem test
  (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
  (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
  (A : Matrix (Fin d) (Fin n) ℝ)
  (k : Fin (d + 2) → ℝ)
  (v : Fin (d + 1) → ℝ)
  (a : Fin d → ℝ)
  (S1 : Solution (originalBezier n d K V A k v a))
  (S2 : Solution (convexBezier n d K V A k v a)) :
  S1.point.1 = S2.point.1 := by {
    rcases S1 with ⟨⟨x1, T1⟩, ⟨hT1, hk1, hv1, ha1⟩, hopt1⟩
    rcases S2 with ⟨⟨x2, T2, y2⟩, ⟨hT2, hk2, hv2, ha2, hy2⟩, hopt2⟩
    simp at hT1 hk1 hv1 ha1 hopt1 hT2 hk2 hv2 ha2 hy2 hopt2 ⊢ 
    -- not true ?
    sorry
  }

end TrajectoryOptimization