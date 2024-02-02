import Lean
import CvxLean.Lib.Reduction
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Simp
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Debug
import CvxLean.Meta.Reduction
import CvxLean.Meta.TacticBuilder
import CvxLean.Command.Solve.Float.RealToFloatLibrary

/-!
# The `reduction` command

Given a problem `p : Minimization D R` and fresh identifiers `red` and `q`, a user can use the
reduction command as follows:
```
reduction red/q : p := by ...
```
Placing the cursor on after the `by` keyword opens up a tactic environment where the goal is to
prove `p ≼ ?q`. After applying a sequence of tactics that transform the goal into, say `r ≼ ?q`,
the user can leave the reduction environment and two new definitions will be added to the
environment:
* `q := r`,
* `red : p ≼ q`.

Writing `reduction'` instead of `reduction` will also generate a backward solution map at the
level of floats.

It is essentially the same as `Command/Equivalence.lean`, except that the goal is to prove a
reduction instead of an equivalence. We note that proving that two problems are equivalent is
usually preferred.
-/

namespace CvxLean

open Lean Elab Meta Tactic Term Command Minimization

/-- Run a transformation tactic indicating that a reduction is expected. -/
def runReductionTactic (mvarId : MVarId) (stx : Syntax) : TermElabM Unit :=
  runTransformationTactic TransformationGoal.Reduction mvarId stx

/-- Run reduction tactic and return both the right-hand term (`q`) and the reduction proof, of
type `Reduction p q`. -/
def elabReductionProof (lhs : Expr) (rhsName : Name) (stx : Syntax) : TermElabM (Expr × Expr) :=
  elabTransformationProof TransformationGoal.Reduction lhs rhsName stx

syntax (name := reduction)
  "reduction" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

syntax (name := reductionAndBwdMap)
  "reduction'" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

/-- Open a reduction environment with a given left-hand-side problem (`lhsStx`) and perhaps some
parameters (`xs`). From this, a reduction goal is set to a target problem which is represented by a
metavariable. The proof (`proofStx`) is evaluated to produce the desired reduction. The metavariable
is then instantiated and the resulting problem is stored using the identifier `probIdStx`. The
reduction witness is stored according to the identifier `redIdStx`. Optionally, a floating-point
backward solution map is created. See `evalReduction` and `evalReductionAndBwdMap`. -/
def evalReductionAux (probIdStx redIdStx : TSyntax `ident) (xs : Array (Syntax × Expr))
    (lhsStx : Syntax) (proofStx : TSyntax `Lean.Parser.Term.byTactic) (bwdMap : Bool) :
    TermElabM Unit := do
  let D ← Meta.mkFreshTypeMVar
  let R ← Meta.mkFreshTypeMVar
  let lhsTy := mkApp2 (Lean.mkConst ``Minimization) D R
  let lhs ← elabTermAndSynthesizeEnsuringType lhsStx (some lhsTy)

  -- NOTE: `instantiateMVars` does not infer the preorder instance.
  for mvarId in ← getMVars lhs do
    try {
      let mvarVal ← synthInstance (← mvarId.getDecl).type
      mvarId.assign mvarVal }
    catch _ => pure ()

  let rhsName := probIdStx.getId
  let (rhs, eqv) ← elabReductionProof lhs rhsName proofStx

  -- Names for new definitions.
  let currNamespace ← getCurrNamespace
  let probId := currNamespace ++ probIdStx.getId
  let redId := currNamespace ++ redIdStx.getId

  -- Add reduced problem to the environment.
  let rhs ← instantiateMVars rhs
  let rhs ← mkLambdaFVars (xs.map Prod.snd) rhs
  let rhs ← instantiateMVars rhs
  simpleAddDefn probId rhs

  -- Add reduction proof to the environment.
  let eqv ← instantiateMVars eqv
  let eqv ← mkLambdaFVars (xs.map Prod.snd) eqv
  let eqv ← instantiateMVars eqv
  simpleAddDefn redId eqv

  if bwdMap then
    lambdaTelescope eqv fun eqvArgs eqvBody => do
      -- Get psi, reduce it appropriately and convert to float.
      let psi := (← whnf eqvBody).getArg! 7

      let mut simpCtx ← Simp.Context.mkDefault
      simpCtx := { simpCtx with config := aggressiveSimpConfig }

      let (.some redExt) ← getSimpExtension? `red |
        throwReductionError "could not find `red` simp extension."

      let (.some equivExt) ← getSimpExtension? `equiv |
        throwReductionError "could not find `equiv` simp extension."

      let mut simpEqvThms ← equivExt.getTheorems
      simpEqvThms ← simpEqvThms.addDeclToUnfold ``Minimization.Equivalence.mk
      simpEqvThms ← simpEqvThms.addDeclToUnfold ``Minimization.Equivalence.psi
      let mut simpRedThms ← redExt.getTheorems
      simpRedThms ← simpRedThms.addDeclToUnfold ``Minimization.Reduction.mk
      simpRedThms ← simpRedThms.addDeclToUnfold ``Minimization.Reduction.psi
      simpRedThms ← simpRedThms.addDeclToUnfold ``Eq.mp
      simpRedThms ← simpRedThms.addDeclToUnfold ``Eq.mpr

      simpCtx := { simpCtx with simpTheorems := #[simpRedThms, simpEqvThms] }

      let (res, _) ← simp psi simpCtx

      -- NOTE: We ignore arguments with `Prop`s here as keeping them would only mean requiring
      -- proofs about floats.
      let redNonPropArgs ← eqvArgs.filterM fun arg => do
        return !(← inferType (← inferType arg)).isProp
      let psi ← mkLambdaFVars redNonPropArgs res.expr
      trace[CvxLean.debug] "psi: {psi}"

      try
        let psiF ← realToFloat psi
        Lean.simpleAddAndCompileDefn (redId ++ `backward_map) psiF
      catch e =>
        trace[CvxLean.debug]
          "`reduction` warning: failed to create `{redId}.backward_map`.\n{e.toMessageData}"

/-- Create `reduction` command. It is similar to the `equivalence` command, but requires a
`Reduction` instead of an `Equivalence`.  -/
@[command_elab «reduction»]
def evalReduction : CommandElab := fun stx => match stx with
  | `(reduction $eqvId / $probId $declSig := $proofStx) => do
      liftTermElabM do
        let (binders, lhsStx) := expandDeclSig declSig.raw
        elabBindersEx binders.getArgs fun xs =>
          evalReductionAux probId eqvId xs lhsStx proofStx false
  | _ => throwUnsupportedSyntax

/-- Same as `reduction` but also adds the backward map to the environment. -/
@[command_elab «reductionAndBwdMap»]
def evalReductionAndBwdMap : CommandElab := fun stx => match stx with
  | `(reduction' $eqvId / $probId $declSig := $proofStx) => do
      liftTermElabM do
        let (binders, lhsStx) := expandDeclSig declSig.raw
        elabBindersEx binders.getArgs fun xs =>
          evalReductionAux probId eqvId xs lhsStx proofStx true
  | _ => throwUnsupportedSyntax

end CvxLean
