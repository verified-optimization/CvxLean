import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Tactic.Conv.ConvOpt

noncomputable section Rules

open CvxLean Minimization Real

def invExpObj := 
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to 
      h : 1 ≤ x

syntax (name := time_cmd) "time_cmd " command : command

@[command_elab «time_cmd»]
def evalTimeCmd : Lean.Elab.Command.CommandElab := fun stx => match stx with
| `(time_cmd $cmd) => do
  let before ← BaseIO.toIO IO.monoMsNow
  Lean.Elab.Command.elabCommand cmd
  let after ← BaseIO.toIO IO.monoMsNow
  let diff := after - before
  IO.println s!"{diff} ms"
| _ => Lean.Elab.throwUnsupportedSyntax

time_cmd reduction invExpObjRedAuto/invExpObjAuto : invExpObj := by
  unfold invExpObj
  convexify
  exact done

-- def rewrite_objective [Preorder R] {cs : D → Prop}
-- {f : D → R}
-- {g : D → R}
-- (hfg : ∀ x, cs x → f x = g x)
-- (sol : Solution
--     { objFun := g
--       constraints := cs })  :
-- Solution {objFun := f, constraints := cs} :=
-- simple_reduction _ _ sol id id
--   (fun {x} hx => le_of_eq (hfg x hx).symm)
--   (fun {x} hx => le_of_eq (hfg x hx))
--   (fun {x} hx => hx)
--   (fun {x} hx => hx)

time_cmd reduction invExpObjRedManual/invExpObjManual : invExpObj := by
  unfold invExpObj
  map_objFun_log
  --apply rewrite_objective (f := fun x => log (1 / exp x)) (g := fun x => (log (exp (-x)))) (hfg := fun x cs => by dsimp; rw [←Real.exp_neg2])
  simp only [←Real.exp_neg2]
  simp only [Real.log_exp]

end Rules 