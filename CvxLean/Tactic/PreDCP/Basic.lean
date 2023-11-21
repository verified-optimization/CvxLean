import Lean
import CvxLean.Lib.Minimization
import CvxLean.Lib.Equivalence
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Tactic.DCP.AtomLibrary.All

namespace CvxLean

/-- Domains with exponentials. -/
class ExpMap (α : Type u) :=
  (exp : α → α)

noncomputable instance : ExpMap ℝ :=
  ⟨Real.exp⟩

noncomputable instance : ExpMap (Fin n → ℝ) :=
  ⟨fun x i => Real.exp (x i)⟩

instance [ExpMap α] [ExpMap β] : ExpMap (α × β) :=
  ⟨fun x => ⟨ExpMap.exp x.1, ExpMap.exp x.2⟩⟩

/-- Domains with fine-grained exponentials. -/
class ExpMapAt (α : Type u) :=
  (exp : ℕ → α → α)

noncomputable instance : ExpMapAt ℝ :=
  ⟨fun _ => Real.exp⟩

instance [ExpMapAt α] [ExpMapAt β] : ExpMapAt (α × β) where
  exp
    | 0, x => ⟨ExpMapAt.exp 0 x.1, x.2⟩
    | n + 1, x => ⟨x.1, ExpMapAt.exp n x.2⟩

/-- Domains with logarithms. -/
class LogMap (α : Type u) :=
  (log : α → α)

noncomputable instance : LogMap ℝ :=
  ⟨Real.log⟩

noncomputable instance : LogMap (Fin n → ℝ) :=
  ⟨fun x i => Real.log (x i)⟩

instance [LogMap α] [LogMap β] : LogMap (α × β) :=
  ⟨fun x => ⟨LogMap.log x.1, LogMap.log x.2⟩⟩

/-- Domains with fine-grained logarithms. -/
class LogMapAt (α : Type u) :=
  (log : ℕ → α → α)

noncomputable instance : LogMapAt ℝ :=
  ⟨fun _ => Real.log⟩

instance [LogMapAt α] [LogMapAt β] : LogMapAt (α × β) where
  log
    | 0, x => ⟨LogMapAt.log 0 x.1, x.2⟩
    | n + 1, x => ⟨x.1, LogMapAt.log n x.2⟩

/-- Domains with exponentials and logarithms with properties. -/
class LogExp (α : Type u) :=
  (log : α → α)
  (exp : α → α)
  (log_exp : ∀ x, log (exp x) = x)
  (exp_log_cond : α → Prop)
  (exp_log : ∀ {x}, exp_log_cond x → exp (log x) = x)

noncomputable instance : LogExp ℝ where
  log := Real.log
  exp := Real.exp
  log_exp := Real.log_exp
  exp_log_cond := fun x => 0 < x
  exp_log := Real.exp_log

noncomputable instance : LogExp (Fin n → ℝ) where
  log := fun x i => Real.log (x i)
  exp := fun x i => Real.exp (x i)
  log_exp := fun x => funext <| fun i => Real.log_exp (x i)
  exp_log_cond := fun x => ∀ i, 0 < x i
  exp_log := fun x => funext <| fun i => Real.exp_log (x i)

noncomputable instance [LogExp α] [LogExp β] : LogExp (α × β) where
  log := fun x => ⟨LogExp.log x.1, LogExp.log x.2⟩
  exp := fun x => ⟨LogExp.exp x.1, LogExp.exp x.2⟩
  log_exp := fun x => by simp [LogExp.log_exp]
  exp_log_cond := fun x => LogExp.exp_log_cond x.1 ∧ LogExp.exp_log_cond x.2
  exp_log := fun x => by
    simp [LogExp.exp_log]
    rw [LogExp.exp_log x.1, LogExp.exp_log x.2]

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

/-- Machinery to perform the change of variables x ↦ e^u. -/

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

/-- Same as `map_exp` but at a particular position in the domain product. -/

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

/-- Tactic `map_objFun_sq` used to square the objective function attempting to
prove all the side conditions with simple tactics. -/

-- TODO: Move.
lemma _root_.Real.pow_two_le_pow_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 ≤ y ^ 2 ↔ x ≤ y := by
  rw [rpow_two, rpow_two, sq_le_sq, abs_of_nonneg hx, abs_of_nonneg hy]

elab (name := prove_pow_two_le_pow_two) "prove_pow_two_le_pow_two" : tactic => do
  let mvarId ← getMainGoal
  let (_, mvarId) ← mvarId.intros
  let mvarId ← mvarId.casesAnd
  let mvarIds ← evalTacticAt (←
    `(tactic|
        rw [← Real.pow_two_le_pow_two (by positivity) (by positivity)] <;>
        try { assumption } <;> try { field_simp } <;> try { positivity })) mvarId
  replaceMainGoal mvarIds

macro "map_objFun_sq" : tactic =>
  `(tactic|
      apply map_objective (g := fun x => x ^ (2 : ℝ)) (hg := by prove_pow_two_le_pow_two) <;>
      dsimp only [Function.comp])

end Tactic

end CvxLean
