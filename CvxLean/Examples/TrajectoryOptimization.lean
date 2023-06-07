import CvxLean.Command.Reduction
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real

noncomputable section TrajectoryOptimization

def problem1 (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin m) → ℝ) :=
  optimization (x : Fin n → ℝ) (T : ℝ) 
    minimize T 
    subject to 
      hT : 1 ≤ T -- 0 < T but can be rescaled?
      hk : K.vecMul x ≤ k 
      hv : V.vecMul x ≤ T • v
      ha : A.vecMul x ≤ T ^ 2 • a

def problem2 (K V A : Matrix (Fin n) (Fin m) ℝ) (k v a : (Fin m) → ℝ) :=
  optimization (x : Fin n → ℝ) (T : ℝ) (y : ℝ) 
    minimize y - T 
    subject to 
      hT : 1 ≤ T
      hk : K.vecMul x ≤ k 
      hv : V.vecMul x ≤ T • v
      ha : A.vecMul x ≤ y • a
      hy : T ^ 2 ≤ y

def K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -1
def V : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => -1
def A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
def k : (Fin 1) → ℝ := fun _ => -1
def v : (Fin 1) → ℝ := fun _ => -2
def a : (Fin 1) → ℝ := fun _ => 1

def sol1 : Solution (problem1 K V A k v a) := 
  { point := ⟨4, 2⟩,
    feasibility := by 
      simp [K, V, A, k, v, a, problem1, vecMul, dotProduct, Pi.hasLe, constraints]
      simp [OfNat.ofNat]
      norm_num,
    optimality := by 
      rintro ⟨⟨x, T⟩, hc⟩
      simp [K, V, A, k, v, a, problem1, vecMul, dotProduct, Pi.hasLe, constraints, objFun] at hc ⊢
      rcases hc with ⟨hT, hk, hv, ha⟩
      have h := le_trans hv ha 
      rw [pow_two] at h
      exact le_of_mul_le_mul_left h (lt_of_lt_of_le zero_lt_one hT)
  }

def sol2 : Solution (problem2 K V A k v a) := 
  { point := ⟨2, 1, 2⟩,
    feasibility := by 
      simp [K, V, A, k, v, a, problem2, vecMul, dotProduct, Pi.hasLe, constraints]
      simp [OfNat.ofNat]
      norm_num,
    optimality := by 
      rintro ⟨⟨x, T, y⟩, hc⟩
      simp [K, V, A, k, v, a, problem2, vecMul, dotProduct, Pi.hasLe, constraints, objFun] at hc ⊢
      rcases hc with ⟨hT, hk, hv, ha, hy⟩
      linarith
  }

end TrajectoryOptimization
