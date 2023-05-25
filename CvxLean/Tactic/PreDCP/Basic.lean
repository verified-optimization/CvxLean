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
      simp only [Function.comp])

elab "prove_exp_log" : tactic => do
  let g ← getMainGoal 
  let (_, g) ← g.intros
  let g ← g.casesAnd
  let gs ← evalTacticAt (← 
    `(tactic| 
        simp [LogMap.log, ExpMap.exp];
        convert rfl <;> rw [exp_log (by assumption)])) g
  replaceMainGoal gs

macro "map_exp" : tactic =>
  `(tactic| 
      apply map_domain 
        (g := fun x => ExpMap.exp x)
        (f := fun x => LogMap.log x)
        (hfg := by prove_exp_log) <;>
      simp only [Function.comp, ExpMap.exp, LogMap.log])

open Parser.Tactic

syntax (name := internally_rewrite) "internally_rewrite " rwRule : tactic
@[tactic internally_rewrite]
def evalInternallyRewrite : Tactic := fun stx =>
  match stx with
  | `(tactic| internally_rewrite $thm) => do 
    let g ← getMainGoal
    for i in [:10] do 
      let iStx := Syntax.mkNumLit i.repr
      let gs ← evalTacticAt (← 
        `(tactic| try { convert rfl using $iStx ; rw [$thm]; })) g
      if gs.length == 0 then 
        replaceMainGoal gs
        return ()
  | _ => throwUnsupportedSyntax

end Tactic

end CvxLean
