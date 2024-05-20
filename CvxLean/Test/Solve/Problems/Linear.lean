import CvxLean.Command.Solve

/-!
Some linear programs.
-/

section Linear

open CvxLean Minimization Real

noncomputable def linear1 :=
  optimization (x : ℝ)
    maximize (7 * x + 1)
    subject to
      h : 2 * x ≤ 3

solve linear1

#print linear1.conicForm

#eval linear1.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval linear1.value    -- 11.500000
#eval linear1.solution -- 1.500000

noncomputable def linear2 :=
  optimization (x y : ℝ)
    minimize 40 * x + 30 * y
    subject to
      c₁ : 12 ≤ x + y
      c₂ : 16 ≤ 2 * x + y

example : linear2 =
    Minimization.mk
      (fun p => 40 * p.1 + 30 * p.2)
      (fun p => 12 ≤ p.1 + p.2 ∧ 16 ≤ 2 * p.1 + p.2) :=
  rfl

def linear2Solution : Solution linear2 :=
  { point := ⟨4, 8⟩,
    isOptimal := by
      split_ands <;> try norm_num
      intros x' y' h_feas
      simp [feasible, linear2] at h_feas ⊢
      linarith }

solve linear2

#print linear2.conicForm

#eval linear2.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval linear2.value    -- 400.000000
#eval linear2.solution -- (4.000000, 8.000000)

noncomputable def linear3 :=
  optimization (x : Fin 2 → ℝ)
    minimize (5 * (x 0) - 4 * (x 1))
    subject to
      h₁ : 3 ≤ (x 0) + (x 1)
      h₂ : (x 1) ≤ 7 + (x 0)

solve linear3

#print linear3.conicForm

#eval linear3.status     -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval linear3.value      -- -30.000000
#eval linear3.solution 0 -- -2.000000
#eval linear3.solution 1 -- 5.000000

noncomputable def linear4 :=
  optimization (x : Fin 5 → ℝ) (y z : ℝ)
    minimize (Vec.sum x + 10 * (y + z))
    subject to
      h₁ : 4.0 ≤ y
      h₂ : 2.5 ≤ z
      h₃ : y + z ≤ Vec.sum x

solve linear4

#print linear4.conicForm

#eval linear4.status       -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval linear4.value        -- 71.500000
#eval linear4.solution.1 0 -- 6.500000
#eval linear4.solution.1 1 -- 0.000000
#eval linear4.solution.1 2 -- 0.000000
#eval linear4.solution.1 3 -- 0.000000
#eval linear4.solution.1 4 -- 0.000000
#eval linear4.solution.2.1 -- 4.000000
#eval linear4.solution.2.2 -- 2.500000

@[optimization_param]
noncomputable def A5 : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    (#[#[ 0.51417013, -1.40067196,  0.71943208,  0.58510080]
     , #[-0.53401066,  1.65680551,  0.13519183,  0.29269704]
     , #[ 0.39224659, -0.61942485,  1.73666095,  2.46240110]
     , #[ 1.76713469,  0.61389781,  0.80559111, -0.12640489]][i.val]!)[j.val]!

@[optimization_param]
noncomputable def b5 : Fin 4 → ℝ :=
  fun i => #[ 10.56567387,  21.07609985,  23.43361457,  15.14706378][i.val]!

@[optimization_param]
noncomputable def c5 : Fin 4 → ℝ :=
  fun i => #[ 0.14794342, -0.19493149,  0.31361829,  1.13959857][i.val]!

open Matrix

noncomputable def linear5 :=
  optimization (x : Fin 4 → ℝ)
    maximize (c5 ⬝ᵥ x)
    subject to
      h₁ : A5.mulVec x ≤ b5
      h₂ : 0 ≤ x

solve linear5

#print linear5.conicForm

#eval linear5.status     -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval linear5.value      -- 11.814741
#eval linear5.solution 0 -- 0.000005
#eval linear5.solution 1 -- 10.569962
#eval linear5.solution 2 -- 0.000000
#eval linear5.solution 3 -- 12.175479

end Linear
