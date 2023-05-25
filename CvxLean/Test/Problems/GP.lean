import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Basic

section GP

open CvxLean Minimization Real

noncomputable def gp :=
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x
      h5 : x <= 3 
      h6 : x^2 + 3 * y / z <= x^0.5
      h7 : x * y = z

reduction red/gp2 : gp := by 
  unfold gp
  map_objFun_log
  map_exp
  have heq₁ : Solution
    (optimization (x : ℝ) (y : ℝ) (z : ℝ) 
      minimize Real.log (exp x / exp y)
      subject to
        h1 : 0 < exp x
        h2 : 0 < exp y
        h3 : 0 < exp z
        h4 : 2 ≤ exp x
        h5 : exp x ≤ 3
        h6 : exp x ^ 2 + 3 * exp y / exp z ≤ exp x ^ OfScientific.ofScientific 5 true 1
        h7 : exp x * exp y = exp z
      ) = 
    Solution
    (optimization (x : ℝ) (y : ℝ) (z : ℝ) 
      minimize Real.log (exp (x - y))
      subject to
        h1 : 0 < exp x
        h2 : 0 < exp y
        h3 : 0 < exp z
        h4 : 2 ≤ exp x
        h5 : exp x ≤ 3
        h6 : exp x ^ 2 + 3 * exp y / exp z ≤ exp x ^ OfScientific.ofScientific 5 true 1
        h7 : exp x * exp y = exp z
    ) := by {
      internally_rewrite ←Real.exp_sub
    }
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
