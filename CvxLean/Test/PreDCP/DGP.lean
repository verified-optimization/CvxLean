import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Lib.Equivalence

noncomputable section GP

open CvxLean Minimization Real

-- section GP1

-- def gp1 :=
--     optimization (x : ℝ)
--       minimize (x)
--       subject to
--         h1 : 0 < x
--         h2 : x ^ 2 ≤ 10.123

-- reduction red1/dcp1 : gp1 := by
--   map_exp
--   convexify
--   exact done

-- #print dcp1
-- -- def dcp1 : Minimization ℝ ℝ :=
-- -- optimization (x : ℝ) 
-- --   minimize x
-- --   subject to
-- --     _ : exp (x * 2) ≤ 10123 / 1000

-- end GP1

-- section GP2

-- def gp2 :=
--     optimization (x y : ℝ)
--       minimize (x)
--       subject to
--         h1 : 0 < x
--         h2 : 0 < y
--         h3 : x * y ≤ 5.382

-- reduction red2/dcp2 : gp2 := by
--   map_exp
--   convexify
--   exact done

-- #print dcp2
-- -- def dcp2 : Minimization (ℝ × ℝ) ℝ :=
-- -- optimization (x : ℝ) (y : ℝ) 
-- --   minimize x
-- --   subject to
-- --     _ : exp (x + y) ≤ 2691 / 500

-- end GP2

-- section GP3 

-- def gp3 := 
--   optimization (x y z : ℝ) 
--     minimize (x / y)
--     subject to 
--       h1 : 0 < x
--       h2 : 0 < y
--       h3 : 0 < z
--       h4 : 2 <= x 
--       h5 : x <= 3
--       h6 : x ^ 2 + 6 * y / z <= sqrt x
--       h7 : x * y = z

-- reduction red3/dcp3 : gp3 := by
--   map_exp
--   convexify
--   exact done

-- #print dcp3
-- -- def dcp3 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- -- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
-- --   minimize x - y
-- --   subject to
-- --     _ : log 2 ≤ x
-- --     _ : exp x ≤ 3
-- --     _ : exp (2 * x - 1 / 2 * x) + 6 * exp (y - z + -(x * (1 / 2))) ≤ 1
-- --     _ : x + y = z

-- end GP3

-- /- https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (4). -/
-- section GP4

-- -- NOTE(RFM): `maximize` does not work because it is set to `Neg.neg`.
-- def gp4 :=
--   optimization (x y z : ℝ) 
--     minimize 1 / (x / y)
--     subject to 
--       h1 : 0 < x
--       h2 : 0 < y
--       h3 : 0 < z
--       h4 : 2 <= x
--       h5 : x <= 3 
--       h6 : x^2 + 3 * y / z <= sqrt x
--       h7 : x / y = z ^ 2

-- reduction red4/dcp4 : gp4 := by 
--   map_exp
--   convexify
--   exact done

-- #print dcp4
-- -- def dcp4 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- -- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
-- --   minimize y - x
-- --   subject to
-- --     _ : log 2 ≤ x
-- --     _ : exp x ≤ 3
-- --     _ : exp (x * (3 / 2)) + 3 * exp (y - z - 1 / 2 * x) ≤ 1
-- --     _ : x - y = 2 * z

-- end GP4

-- /- In https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (5) and in
-- https://www.cvxpy.org/examples/dgp/max_volume_box.html -/
-- section GP5

-- @[optimization_param] def Awall : ℝ := 100
-- @[optimization_param] def Aflr : ℝ := 10
-- @[optimization_param] def α : ℝ := 0.5
-- @[optimization_param] def β : ℝ := 0.5
-- @[optimization_param] def γ : ℝ := 5
-- @[optimization_param] def δ : ℝ := 6

-- -- NOTE(RFM): We need to provide proofs of positivity. For now, we just add 
-- -- them as simp lemmas.
-- @[simp] lemma α_pos : 0 < α := by unfold α; norm_num
-- @[simp] lemma β_pos : 0 < β := by unfold β; norm_num
-- @[simp] lemma γ_pos : 0 < γ := by unfold γ; norm_num
-- @[simp] lemma δ_pos : 0 < δ := by unfold δ; norm_num

-- -- NOTE(RFM): `maximize` issue.
-- def gp5 :=
--   optimization (h w d : ℝ) 
--     minimize (1 / (h * w * d))
--     subject to 
--       h1 : 0 < h
--       h2 : 0 < w
--       h3 : 0 < d
--       h4 : 2 * (h * d + w * d) ≤ Awall
--       h5 : w * d ≤ Aflr
--       h6 : α ≤ h/w
--       h7 : h/w ≤ β  
--       h8 : γ ≤ d/w
--       h9 : d/w ≤ δ

-- reduction red5/dcp5 : gp5 := by
--   map_exp
--   convexify
--   exact done

-- #print dcp5
-- -- def dcp5 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- -- optimization (h : ℝ) (w : ℝ) (d : ℝ) 
-- --   minimize -d + -w + -h
-- --   subject to
-- --     _ : 2 * exp (h + d) + 2 * exp (w + d) ≤ Awall
-- --     _ : exp (w + d) ≤ Aflr
-- --     _ : log α ≤ h - w
-- --     _ : exp (h - w) ≤ β
-- --     _ : log γ ≤ d - w
-- --     _ : d ≤ log δ + w

-- end GP5

-- /- In https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf section 2.2. -/
-- section GP6

-- -- NOTE(RFM): We don't have the power atom yet.
-- -- objFun : (x ^ (-1)) * y ^ (-1 / 2) * z ^ (-1) + 2.3 * x * z + 4 * x * y * z
-- -- h4 : (1 / 3) * x ^ (-2) * y ^ (-2) + (4 / 3) * y ^ (1 / 2) * z ^ (-1) ≤ 1
-- def gp6 := 
--   optimization (x y z : ℝ) 
--     minimize (1 / x) * (1 / sqrt y) * (1 / z) + (2.3) * x * z + 4 * x * y * z
--     subject to 
--       h1 : 0 < x
--       h2 : 0 < y
--       h3 : 0 < z
--       h4 : (1 / 3) * (1 / (x ^ 2)) * (1 / (y ^ 2)) + (4 / 3) * (sqrt y) * (1 / z) ≤ 1
--       h5 : x + 2 * y + 3 * z ≤ 1
--       h6 : (1 / 2) * x * y = 1

-- set_option maxHeartbeats 1000000
-- reduction red6/dcp6 : gp6 := by
--   map_exp
--   convexify
--   exact done

-- #print dcp6
-- -- def dcp3 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- -- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
-- --   minimize exp (-(y * (1 / 2)) - x - z) + (23 * (exp (z + x) / 10) + 4 * exp (y + (z + x)))
-- --   subject to
-- --     _ : 1 / 3 * exp (-(y * 2) + -(2 * x)) + 1 / 3 * (4 * exp (y * (1 / 2) - z)) ≤ 1
-- --     _ : exp x + (exp y * 2 + exp z * 3) ≤ 1
-- --     _ : y + (x - log 2) = 0

-- end GP6 

section GP7

@[optimization_param] def σ : Fin 5 → ℝ := fun _ => 0.5
@[optimization_param] def Pmin : Fin 5 → ℝ := fun _ => 0.1
@[optimization_param] def Pmax : Fin 5 → ℝ := fun _ => 5 
@[optimization_param] def SINRmin : ℝ := 0.2
@[optimization_param] def G : Matrix (Fin 5) (Fin 5) ℝ := fun i j => 
   (#[#[ 1.0,  0.1, 0.2, 0.1, 0.05]
    , #[ 0.1,  1.0, 0.1, 0.1, 0.05]
    , #[ 0.2,  0.1, 1.0, 0.2,  0.2]
    , #[ 0.1,  0.1, 0.2, 1.0,  0.1]
    , #[0.05, 0.05, 0.2, 0.1,  1.0]][i]!)[j]!

lemma G_diag_pos : ∀ i, 0 < G i i := by
  intro i; simp [G]
  fin_cases i <;> simp [getElem!, Array.getElem_eq_data_get] <;> norm_num

lemma G_symm : ∀ i j, G i j = G j i := by
  intro i j; simp [G]
  fin_cases i <;> fin_cases j <;> simp [getElem!, Array.getElem_eq_data_get]

open BigOperators

def gp7 := 
  optimization (P : Fin 5 → ℝ) 
    minimize Vec.sum P --∑ i, P i 
    subject to 
      h1 : ∀ i, 0 < P i
      h2 : Pmin ≤ P
      h3 : P ≤ Pmax
      h4 : ∀ i, ((σ i + ∑ k, if i ≠ k then G i k * P k else 0) / (G i i * P i)) ≤ 1 / SINRmin
      -- NOTE(RFM): Work in vector notaton, avoiding functions and bvars.
      -- TODO(RFM): Add diagonal and diag to the atom library.
      -- h5 : (σ + (G - (Matrix.diagonal G.diag)).vecMul P) ≤ 
      --      (1 / SINRmin) • ((Matrix.diagonal G.diag).vecMul P)

def gp7' := 
  optimization (P : Fin 5 → ℝ) 
    minimize Vec.sum P
    subject to 
      h1 : ∀ i, 0 < P i
      h2 : Pmin ≤ P
      h3 : P ≤ Pmax
      h5 : σ + ((G - (Matrix.diagonal G.diag)) - (1 / SINRmin) • (Matrix.diagonal G.diag)).vecMul P ≤ 0

def equiv7 : MinEquiv gp7 gp7' := {
  phi := id,
  psi := id,
  phi_feasibility := fun P hP => by {
    simp only [gp7, gp7', constraints] at hP ⊢
    rcases hP with ⟨hPpos, hPmin, hPmax, hle⟩
    refine ⟨hPpos, hPmin, hPmax, ?_⟩
    intros i 
    have hlei := hle i
    simp at hlei ⊢
    simp [Matrix.vecMul, Matrix.dotProduct, Matrix.diagonal, Matrix.diag]
    rw [div_le_iff (mul_pos (G_diag_pos i) (hPpos i))] at hlei
    have sum_mul_sub : ∀ (a b : Fin 5 → ℝ), 
      ∑ k, P k * ((a k) - (b k)) = 
      ∑ k, P k * (a k) - ∑ k, P k * b k := fun a b => by
      rw [←Finset.sum_sub_distrib]
      apply congr_arg; ext k
      rw [mul_sub]
    rw [sum_mul_sub]
    have sum_mul_ite_eq : 
      (∑ k, P k * if k = i then SINRmin⁻¹ * G k k else 0) = 
      SINRmin⁻¹ * (G i i * P i) := by 
      simp [mul_comm (P i) _, mul_assoc _ _ (P i)]
    rw [sum_mul_ite_eq]
    have sum_mul_nondiagonal : 
      ∑ k, P k * (G k i - if k = i then G k k else 0) = 
      ∑ k, if i = k then 0 else G i k * P k := by
      apply congr_arg; ext k
      simp [mul_ite, @eq_comm _ k i]
      by_cases i = k <;> simp [h]
      rw [G_symm k i, mul_comm]
    rw [sum_mul_nondiagonal]
    rw [add_sub, sub_le_iff_le_add, zero_add]
    exact hlei
  }
  psi_feasibility := fun P hP => by {
    sorry
  }
  phi_optimality := fun P hP => by simp [gp7, gp7']
  psi_optimality := fun P hP => by simp [gp7, gp7']
}

set_option trace.Meta.debug true

lemma test : Solution gp7 := by 
  unfold gp7 
  -- map_exp

  -- TODO(RFM): remove_constr is buggy, applying withLambdaBody after it fails,
  -- potentially because the term built is not a simple lambda term.
  -- conv_constr => 
  --   { rw [eq_true (fun _ => by positivity : ∀ _, _ < _)] }
  -- conv in (True ∧ _) => rw [true_and]
  dcp
  -- convexify
  sorry

end GP7

namespace GP8 
-- h_min = 1
--     h_max = 10
--     w_min = 1
--     w_max = 10
--     R_max = 2
--     F_1 = 10
--     F_2 = 10 
--     sigma = 0.01

--     A8 = cp.Variable(pos=True)
--     h8 = cp.Variable(pos=True)
--     w8 = cp.Variable(pos=True)
--     r8 = cp.Variable(pos=True)

--     dgp8 = cp.Problem(
--         cp.Minimize(2 * A8 * cp.sqrt(w8 ** 2 + h8 ** 2)), [
--             F_1 * cp.sqrt(w8 ** 2 + h8 ** 2) / 2 * h8 <= sigma * A8,
--             F_2 * cp.sqrt(w8 ** 2 + h8 ** 2) / 2 * w8 <= sigma * A8,
--             h_min <= h8,
--             h8 <= h_max,
--             w_min <= w8,
--             w8 <= w_max,
--             0.21 * r8 ** 2 <= A8 / (2 * np.pi),
--             cp.sqrt(A8 / (2 * np.pi) + r8 ** 2) <= R_max,
--         ])

@[optimization_param] def hmin : ℝ := 1
@[optimization_param] def hmax : ℝ := 10
@[optimization_param] def wmin : ℝ := 1
@[optimization_param] def wmax : ℝ := 10
@[optimization_param] def Rmax : ℝ := 2
@[optimization_param] def F₁ : ℝ := 10
@[optimization_param] def F₂ : ℝ := 10
@[optimization_param] def σ : ℝ := 0.01

def trussDesign := 
  optimization (h w R r : ℝ)
    minimize (2 * (2 * π * (R^2 - r^2)) * (sqrt (w^2 + h^2)))
    subject to 
      h1 : F₁ * sqrt (w^2 + h^2) / 2 * h ≤ σ * (2 * π * (R^2 - r^2))
      h2 : F₂ * sqrt (w^2 + h^2) / 2 * w ≤ σ * (2 * π * (R^2 - r^2))
      h3 : hmin ≤ h
      h4 : h ≤ hmax
      h5 : wmin ≤ w
      h6 : w ≤ wmax
      h7 : 1.1 * r ≤ R
      h8 : R ≤ Rmax

reduction φ/trussDesign₂ : trussDesign := by 
  apply map_domain

end GP8 
