import Lean
import CvxLean.Lib.Minimization
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Tactic.DCP.AtomLibrary

namespace CvxLean

class ExpMap (α : Type u) :=
  (exp : α → α)

noncomputable instance : ExpMap ℝ := 
  ⟨Real.exp⟩

noncomputable instance : ExpMap (Fin n → ℝ) := 
  ⟨fun x i => Real.exp (x i)⟩

instance [ExpMap α] [ExpMap β] : ExpMap (α × β) := 
  ⟨fun x => ⟨ExpMap.exp x.1, ExpMap.exp x.2⟩⟩

class ExpMapAt (α : Type u) := 
  (exp : ℕ → α → α)

noncomputable instance : ExpMapAt ℝ := 
  ⟨fun _ => Real.exp⟩

instance [ExpMapAt α] [ExpMapAt β] : ExpMapAt (α × β) where 
  exp
    | 0, x => ⟨ExpMapAt.exp 0 x.1, x.2⟩
    | n + 1, x => ⟨x.1, ExpMapAt.exp n x.2⟩

class LogMap (α : Type u) :=
  (log : α → α)

noncomputable instance : LogMap ℝ :=
  ⟨Real.log⟩

noncomputable instance : LogMap (Fin n → ℝ) :=
  ⟨fun x i => Real.log (x i)⟩

instance [LogMap α] [LogMap β] : LogMap (α × β) :=
  ⟨fun x => ⟨LogMap.log x.1, LogMap.log x.2⟩⟩

class LogMapAt (α : Type u) :=
  (log : ℕ → α → α)

noncomputable instance : LogMapAt ℝ :=
  ⟨fun _ => Real.log⟩

instance [LogMapAt α] [LogMapAt β] : LogMapAt (α × β) where
  log
    | 0, x => ⟨LogMapAt.log 0 x.1, x.2⟩
    | n + 1, x => ⟨x.1, LogMapAt.log n x.2⟩

namespace Tactic

open Minimization Real

open Lean Meta Elab Tactic
open Lean.Elab.Term

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

elab "prove_exp_log" : tactic => do
  let g ← getMainGoal 
  let (_, g) ← g.intros
  let g ← g.casesAnd
  let gs ← evalTacticAt (← 
    `(tactic| 
        simp [LogMap.log, ExpMap.exp];
        congr <;> funext <;> rw [exp_log (by simp [*] <;> positivity)])) g
  replaceMainGoal gs

macro "make_positive_constraints_true" : tactic => 
  `(tactic|
      conv_constr => repeat { try { rw [eq_true (by positivity : _ < _)] } })

macro "remove_trues" : tactic => 
  `(tactic|
      repeat' conv in (True ∧ _) => rw [true_and])

macro "remove_positive_constraints" : tactic => 
  `(tactic|
      make_positive_constraints_true <;>
      remove_trues)

macro "map_exp" : tactic =>
  `(tactic| 
      apply map_domain 
        (g := fun x => ExpMap.exp x)
        (f := fun x => LogMap.log x)
        (hfg := by prove_exp_log) <;>
      dsimp only [Function.comp, ExpMap.exp, LogMap.log] <;>
      remove_positive_constraints)

elab "prove_exp_log_at" : tactic => do
  let g ← getMainGoal 
  let (_, g) ← g.intros
  let g ← g.casesAnd
  let gs ← evalTacticAt (← 
    `(tactic| 
        simp [LogMapAt.log, ExpMapAt.exp];
        congr <;> rw [exp_log (by assumption)])) g
  replaceMainGoal gs

macro "map_exp_at " i:num : tactic =>
  `(tactic| 
      apply map_domain 
        (g := fun x => ExpMapAt.exp $i x)
        (f := fun x => LogMapAt.log $i x)
        (hfg := by prove_exp_log_at) <;>
      dsimp only [Function.comp, ExpMapAt.exp, LogMapAt.log] <;>
      remove_positive_constraints)

end Tactic

end CvxLean
