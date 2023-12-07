import Lean
import CvxLean.Syntax.Minimization
import CvxLean.Lib.Minimization
import CvxLean.Lib.Math.Data.Real
import CvxLean.Tactic.Arith.Arith

namespace CvxLean

namespace Tactic

open Minimization Real

open Lean Meta Elab Tactic Term

/-- Tactic `map_objFun_log` used to map the logarithm to the objective function
attempting to prove all the side conditions with simple tactics. -/

elab (name := prove_log_le_log) "prove_log_le_log" : tactic => do
  let mvarId ← getMainGoal
  let (_, mvarId) ← mvarId.intros
  let mvarId ← mvarId.casesAnd
  let mvarIds ← evalTacticAt (←
    `(tactic|
        try { simp only [maximizeNeg] };
        refine' (log_le_log _ _).1 _ <;>
        try { assumption } <;> try { field_simp } <;> try { positivity })) mvarId
  replaceMainGoal mvarIds

macro "map_objFun_log" : tactic =>
  `(tactic|
      apply map_objective (g := Real.log) (hg := by prove_log_le_log) <;>
      dsimp only [Function.comp])

/-- Tactic `map_objFun_sq` used to square the objective function attempting to
prove all the side conditions with simple tactics. -/

elab (name := prove_pow_two_le_pow_two) "prove_pow_two_le_pow_two" : tactic => do
  let mvarId ← getMainGoal
  let (_, mvarId) ← mvarId.intros
  let mvarId ← mvarId.casesAnd
  let mvarIds ← evalTacticAt (←
    `(tactic|
        rw [←Real.pow_two_le_pow_two (by positivity) (by positivity)] <;>
        try { assumption } <;> try { field_simp } <;> try { positivity })) mvarId
  replaceMainGoal mvarIds

macro "map_objFun_sq" : tactic =>
  `(tactic|
      apply map_objective (g := fun x => x ^ (2 : ℝ)) (hg := by prove_pow_two_le_pow_two) <;>
      dsimp only [Function.comp])

end Tactic

end CvxLean
