import Lean
import CvxLean.Lib.Minimization
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Tactic.DCP.AtomLibrary

namespace CvxLean

class ExpMap (α : Type u) :=
  (exp : α → α)

noncomputable instance : ExpMap ℝ := 
  ⟨Real.exp⟩

instance [ExpMap α] [ExpMap β] : ExpMap (α × β) := 
  ⟨fun x => ⟨ExpMap.exp x.1, ExpMap.exp x.2⟩⟩

class LogMap (α : Type u) :=
  (log : α → α)

noncomputable instance : LogMap ℝ :=
  ⟨Real.log⟩

instance [LogMap α] [LogMap β] : LogMap (α × β) :=
  ⟨fun x => ⟨LogMap.log x.1, LogMap.log x.2⟩⟩

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
        simp only [maximizeNeg];
        refine' (log_le_log _ _).1 _ <;>
        try { assumption } <;> field_simp <;> positivity)) mvarId
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
        convert rfl <;> rw [exp_log (by assumption)])) g
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

open Parser.Tactic

syntax (name := internally_do) "internally_do " tactic : tactic
@[tactic internally_do]
def evalInternallyDo : Tactic := fun stx =>
  match stx with
  | `(tactic| internally_do $tac) => do 
    for i in [2:10] do 
      let g ← getMainGoal
      let iStx := Syntax.mkNumLit i.repr
      let gs ← evalTacticAt (← 
        `(tactic| try { convert rfl using $iStx <;> $tac })) g
      replaceMainGoal gs
      if gs.length == 0 then 
        return ()
  | _  => throwUnsupportedSyntax

end Tactic

end CvxLean
