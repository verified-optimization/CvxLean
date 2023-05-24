import CvxLean.Command.Solve
import CvxLean.Tactic.Conv.ConvOpt

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

open Lean Meta Elab Tactic
open Lean.Elab.Term

elab "prove_log_le_log" : tactic => do
  let mvarId ← getMainGoal
  let [mvarId] ← evalTacticAt (← `(tactic| intros x y h csy)) mvarId | unreachable!
  let mvarId ← mvarId.casesAnd
  let mvarIds ← evalTacticAt (← 
    `(tactic| 
        simp only [maximizeNeg];
        refine' (log_le_log _ _).1 <;>
        field_simp <;> positivity)) mvarId
  replaceMainGoal mvarIds

macro "map_objFun_log" : tactic => 
  `(tactic| 
      apply map_objective (g := Real.log) (hg := by prove_log_le_log) <;> 
      simp only [Function.comp])

elab "prove_exp_log" : tactic => do
  let mvarId ← getMainGoal
  let [mvarId] ← evalTacticAt (← `(tactic| intros x hcs)) mvarId | unreachable!
  let mvarId ← mvarId.casesAnd
  let mvarIds ← evalTacticAt (← 
    `(tactic| 
        simp [LogMap.log, ExpMap.exp];
        convert rfl <;> rw [exp_log (by assumption)])) mvarId
  replaceMainGoal mvarIds

macro "map_exp" : tactic =>
  `(tactic| 
      apply map_domain 
        (g := fun x => ExpMap.exp x)
        (f := fun x => LogMap.log x)
        (hfg := by prove_exp_log) <;>
      simp only [Function.comp, ExpMap.exp, LogMap.log])

syntax (name := internally_rewrite) "internally_rewrite " Lean.Parser.Tactic.rwRule : tactic
@[tactic internally_rewrite]
def evalInternallyRewrite : Tactic := fun stx =>
  match stx with
  | `(tactic| internally_rewrite $thm) => do 
    let g ← getMainGoal
    for i in [:10] do 
      let iStx := Syntax.mkNumLit i.repr
      let gRes ← evalTacticAt  (← `(tactic| try { convert rfl using $iStx ; rw [$thm]; }))  g
      if gRes.length == 0 then 
        replaceMainGoal gRes
        return ()
  | _ => throwUnsupportedSyntax

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

end GP