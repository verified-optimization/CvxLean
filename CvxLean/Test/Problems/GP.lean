import CvxLean.Command.Solve
import CvxLean.Tactic.Basic.RenameConstr
import CvxLean.Tactic.Basic.RemoveConstr
import CvxLean.Tactic.Conv.ConvOpt

section GP

open CvxLean Minimization Real

attribute [-instance] coeDecidableEq
attribute [-simp] Set.inj_on_empty Set.inj_on_singleton Quot.lift_on₂_mk 
  Quot.lift_on_mk Quot.lift₂_mk

-- Original problem, geometric programming.
noncomputable def problem₁ := 
  optimization (x y : ℝ)
  minimize x * y
  subject to
    h : 10 ≤ x * y 
    hxpos : 0 < x
    hypos : 0 < y

-- Step 1: Change of variables x ↦ exp x, y ↦ exp y.
reduction red₂₁/problem₂ : problem₁ := by 
  -- The tactic state here is:
  --    done: Solution ?m.254
  --    ⊢ Solution problem₁
  -- The idea is that you transform the goal and then unify it with the 
  -- metavariable ?m.254.
  simp [problem₁]
  apply map_domain 
    (f := fun xy => (log xy.fst, log xy.snd))
    (g := fun xy => (exp xy.fst, exp xy.snd))
  case hfg => 
    intros xy hcconstraints
    have hxpos := hcconstraints.1
    have hypos := hcconstraints.2.2
    simp only [exp_log hxpos, exp_log hypos] 
  case sol => 
    simp only [Function.comp]
    exact done

#print problem₂ 
-- optimization (_ : Real) (_ : Real) 
--   minimize exp p.fst * exp p.snd
--   subject to
--     _ : 0 < exp p.fst
--     _ : 10 ≤ exp p.fst * exp p.snd
--     _ : 0 < exp p.snd
#check red₂₁ 
-- Solution problem₂ → Solution problem₁

-- Step 2: Remove positivity constraints. 
-- It is not strictly necessary to do this, but simplifies the next steps. 
reduction red₃₂/problem₃ : problem₂ := by 
  simp [problem₂]
  rename_constr [hxpos]
  remove_constr hxpos 
  . exact exp_pos _ 
  rename_constr [h, hypos]
  remove_constr hypos
  . exact exp_pos _
  exact done

#print problem₃
-- optimization (_ : Real) (_ : Real) 
--   minimize exp p.fst * exp p.snd
--   subject to
--     h : 10 ≤ exp p.fst * exp p.snd
#check red₃₂
-- Solution problem₃ → Solution problem₂

-- Step 3: Rewrite products of exponentials. 
reduction red₄₃/problem₄ : problem₃ := by 
  simp [problem₃]
  apply rewrite_objective  
  case hfg =>
    intros xy _ 
    rw [←exp_add]  
  apply rewrite_constraints
  case hfg =>
    intros xy
    rw [←exp_add]
  exact done 

#print problem₄
-- optimization (_ : Real) (_ : Real) 
--   minimize exp (p.fst + p.snd)
--   subject to
--     _ : 10 ≤ exp (p.fst + p.snd)
#check red₄₃
-- Solution problem₄ → Solution problem₃
  
-- Step 4: Apply logarithm and simplify.
reduction red₅₄/problem₅ : problem₄ := by 
  simp [problem₄]
  apply map_objective (g := log)
  case hg =>
    intros r s _ _ hmono 
    simp [log_exp] at hmono
    exact exp_le_exp.2 hmono 
  simp only [Function.comp]
  apply rewrite_objective
  case hfg =>
    intros xy _ 
    rw [log_exp]
  apply rewrite_constraints
  case hfg =>
    intros xy
    -- This is a mathport issue... 
    have htenpos : @Zero.zero Real hasZero < 10 := by 
      rw [(rfl : @Zero.zero Real hasZero = 0)] 
      apply Nat.cast_pos.mpr 
      norm_num
    have hexpxypos : 0 < exp (xy.fst + xy.snd) := exp_pos _ 
    rw [←log_le_log htenpos hexpxypos]
  apply rewrite_constraints
  case hfg =>
    intros xy
    rw [log_exp]
  case sol => 
    simp only [Function.comp]
    exact done

#print problem₅  
-- optimization (_ : Real) (_ : Real) 
--   minimize p.fst + p.snd
--   subject to
--     _ : log 10 ≤ p.fst + p.snd
#check red₅₄
-- Solution problem₅ → Solution problem₄

-- This is what I need to find, essentially.
noncomputable def phi : Solution problem₅ → Solution problem₁ := 
  red₂₁ ∘ red₃₂ ∘ red₄₃ ∘ red₅₄

-- And now we can call the solver!
solve problem₅

#eval problem₅.status   -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval problem₅.solution -- (2.302585, 0.000000)
#eval problem₅.value    -- 2.302585

-- Unfortunately we cannot really use `phi` right now this because the solution 
-- is not of  type `Solution`, it's just a point. And in fact it's not quite 
-- correct, as exp(2.302585) * exp(0) ≈ 9.99999907006 and not 10. But there are 
-- ways arround this, which is what I'm working on. 

end GP
