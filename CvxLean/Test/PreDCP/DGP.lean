import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

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

open BigOperators

def gp7 := 
  optimization (P : Fin 5 → ℝ) 
    minimize Vec.sum P --∑ i, P i 
    subject to 
      h1 : ∀ i, 0 < P i
      h2 : Pmin ≤ P
      h3 : P ≤ Pmax
      -- h4 : (fun i => (σ i + Vec.sum (fun k => if i ≠ k then G i k * P k else 0)) / (G i i * P i)) ≤ fun _ => 1 / SINRmin
      -- NOTE(RFM): Work in vector notaton, avoiding functions and bvars.
      -- TODO(RFM): Add diagonal and diag to the atom library.
      h5 : (σ + (G - (Matrix.diagonal G.diag)).vecMul P) ≤ 
           (1 / SINRmin) • ((Matrix.diagonal G.diag).vecMul P)

set_option trace.Meta.debug true

lemma test : Solution gp7 := by 
  unfold gp7 
  map_exp

  -- TODO(RFM): remove_constr is buggy, applying withLambdaBody after it fails,
  -- potentially because the term built is not a simple lambda term.
  conv_constr => 
    { rw [eq_true (fun _ => by positivity : ∀ _, _ < _)] }
  conv in (True ∧ _) => rw [true_and]

  convexify
  sorry

end GP7
