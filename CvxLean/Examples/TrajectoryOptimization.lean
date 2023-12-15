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

def relaxationBezier (n d : ℕ)
  (K : Matrix (Fin (d + 2)) (Fin n) ℝ)
  (V : Matrix (Fin (d + 1)) (Fin n) ℝ)
  (A : Matrix (Fin d) (Fin n) ℝ)
  (k : Fin (d + 2) → ℝ)
  (v : Fin (d + 1) → ℝ)
  (a : Fin d → ℝ) :
  Relaxation (originalBezier n d K V A k v a) (convexBezier n d K V A k v a) :=
  { r := fun ⟨x, T⟩ => ⟨x, T, T ^ 2⟩,
    r_injective := fun ⟨x, T⟩ ⟨x', T'⟩ h => by rcases h with ⟨hx, hT, _⟩; rfl,
    r_feasibility := fun ⟨x, T⟩ ⟨hT, hk, hv, ha⟩ => ⟨hT, hk, hv, ha, le_refl _⟩
    r_lower_bound := fun ⟨x, T⟩ ⟨hT, _, _, _⟩ => by {
      simp only [convexBezier, originalBezier]
      rw [sqrt_le_iff]
      have : 0 ≤ T := le_trans zero_le_one hT
      simp [this]
    } }

end TrajectoryOptimization
