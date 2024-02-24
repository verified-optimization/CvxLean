import CvxLean.Tactic.Basic.RemoveConstr
import CvxLean.Tactic.Arith.Arith

/-!
# Tactic to remove trivial constraints

This file defines the `remove_trivial_constrs`. It essentially uses `remove_constr` on every
constraint and tries to establish the proof obligation using the `positivity!` tactic. This is
useful for constraints of the form `0 < exp x`, for example.
-/

namespace CvxLean

open Lean Meta Elab Term Tactic

namespace Meta

/-- Iteratively try to apply `remove_constr` on every constraint. Do nothing if it fails. -/
def removeTrivialConstrsBuilder : EquivalenceBuilder Unit := fun eqvExpr g => g.withContext do
  let lhs ← eqvExpr.toMinimizationExprLHS
  let constrNames ← withLambdaBody lhs.constraints fun _ constrsBody => do
    let cs ← decomposeConstraints constrsBody
    return cs.map fun c => c.1
  let mut g := g
  for n in constrNames do
    let eqvBuilder := removeConstrBuilder n (← `(term| (by positivity!)))
    let gs ← Tactic.run g <|
      Tactic.tryCatch eqvBuilder.toTactic (fun _ => do pure ())
    if gs.length != 1 then
      throwError "`remove_trivial_constrs` error: failed to remove {n}."
    g := gs[0]!

  let gsFinal ← evalTacticAt (← `(tactic| equivalence_rfl)) g
  if gsFinal.length != 0 then
    throwError "`remove_trivial_constrs` error: could not close last goal."

end Meta

namespace Tactic

syntax (name := removeTrivialConstrs) "remove_trivial_constrs" : tactic

@[tactic removeTrivialConstrs]
def evalRemoveTrivialConstrs : Tactic := fun stx => match stx with
  | `(tactic| remove_trivial_constrs) => do
      removeTrivialConstrsBuilder.toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end Tactic

end CvxLean
