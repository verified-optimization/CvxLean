import CvxLean.Lib.Equivalence
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Simp
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Debug
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Command.Solve.Float.RealToFloatLibrary

/-!
# The `equivalence` command

Given a problem `p : Minimization D R` and fresh identifiers `eqv` and `q`, a user can use the
equivalence command as follows:
```
equivalence eqv/q : p := by ...
```
Placing the cursor on after the `by` keyword opens up a tactic environment where the goal is to
prove `p ≡ ?q`. After applying a sequence of tactics that transform the goal into, say `r ≡ ?q`,
the user can leave the equivalence environment and two new definitions will be added to the
environment:
* `q := r`,
* `eqv : p ≡ q`.

Writing `equivalence*` instead of `equivalence` will also generate a backward solution map at the
level of floats.
-/

namespace CvxLean

open Lean Elab Meta Tactic Term Command Minimization

/-- Run a transformation tactic indicating that an equivalence is expected. -/
partial def runEquivalenceTactic (mvarId : MVarId) (stx : Syntax) : TermElabM Unit := do
  runTransformationTactic TransformationGoal.Equivalence mvarId stx

/-- Run equivalence tactic and return both the right-hand term (`q`) and the equivalence proof, of
type `Equivalence p q`. -/
def elabEquivalenceProof (lhs : Expr) (rhsName : Name) (stx : Syntax) : TermElabM (Expr × Expr) :=
  elabTransformationProof TransformationGoal.Equivalence lhs rhsName stx

/-- Open an equivalence environment. -/
syntax (name := equivalence)
  "equivalence" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

/-- Open an equivalence environment and try to generate a computable backward map. -/
syntax (name := equivalenceAndBwdMap)
  "equivalence*" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

/-- Open an equivalence environment with a given left-hand-side problem (`lhsStx`) and perhaps some
parameters (`xs`). From this, an equivalence goal is set to a target problem which is represented by
a metavariable. The proof (`proofStx`) is evaluated to produce the desired equivalence. The
metavariable is then instantiated and the resulting problem is stored using the identifier
`probIdStx`. The equivalence witness is stored according to the identifier `redIdStx`. Optionally, a
floating-point backward solution map is created. See `evalEquivalence` and
`evalEquivalenceAndBwdMap`. -/
def evalEquivalenceAux (probIdStx eqvIdStx : TSyntax `ident) (xs : Array (Syntax × Expr))
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
  let (rhs, eqv) ← elabEquivalenceProof lhs rhsName proofStx

  -- Names for new definitions.
  let currNamespace ← getCurrNamespace
  let probId := currNamespace ++ probIdStx.getId
  let eqvId := currNamespace ++ eqvIdStx.getId

  -- Add equivalent problem to the environment.
  let rhs ← instantiateMVars rhs
  let rhs ← mkLambdaFVars (xs.map Prod.snd) rhs
  let rhs ← instantiateMVars rhs
  simpleAddDefn probId rhs

  -- Add equivalence proof to the environment.
  let eqv ← instantiateMVars eqv
  let eqv ← mkLambdaFVars (xs.map Prod.snd) eqv
  let eqv ← instantiateMVars eqv
  simpleAddDefn eqvId eqv

  if bwdMap then
    lambdaTelescope eqv fun eqvArgs eqvBody => do
      -- Get psi, reduce it appropriately and convert to float.
      let psi := (← whnf eqvBody).getArg! 7
      trace[CvxLean.debug] "psi: {psi}"

      let mut simpCtx ← Simp.Context.mkDefault
      simpCtx := { simpCtx with config := aggressiveSimpConfig }

      let (.some ext) ← getSimpExtension? `equiv |
        throwEquivalenceError "could not find `equiv` simp extension."

      let mut simpThms ← ext.getTheorems
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.mk
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.psi
      simpThms ← simpThms.addDeclToUnfold ``Eq.mp
      simpThms ← simpThms.addDeclToUnfold ``Eq.mpr

      simpCtx := { simpCtx with simpTheorems := #[simpThms] }

      let (res, _) ← simp psi simpCtx

      -- NOTE: We ignore arguments with `Prop`s here as keeping them would only mean requiring
      -- proofs about floats.
      let eqvNonPropArgs ← eqvArgs.filterM fun arg => do
        return !(← inferType (← inferType arg)).isProp
      let psi ← mkLambdaFVars eqvNonPropArgs res.expr
      trace[CvxLean.debug] "simplified psi: {psi}"

      try
        let psiF ← realToFloat psi
        Lean.simpleAddAndCompileDefn (eqvId ++ `backward_map) psiF
      catch e =>
        trace[CvxLean.debug]
          "`equivalence` warning: failed to create `{eqvId}.backward_map`.\n{e.toMessageData}"

/-- Create `equivalence` command. -/
@[command_elab «equivalence»]
def evalEquivalence : CommandElab := fun stx => match stx with
  | `(equivalence $eqvId / $probId $declSig := $proofStx) => do
      liftTermElabM do
        let (binders, lhsStx) := expandDeclSig declSig.raw
        elabBindersEx binders.getArgs fun xs =>
          evalEquivalenceAux probId eqvId xs lhsStx proofStx false
  | _ => throwUnsupportedSyntax

/-- Same as `equivalence` but also adds the backward map to the environment. -/
@[command_elab «equivalenceAndBwdMap»]
def evalEquivalenceAndBwdMap : CommandElab := fun stx => match stx with
  | `(equivalence* $eqvId / $probId $declSig := $proofStx) => do
      liftTermElabM do
        let (binders, lhsStx) := expandDeclSig declSig.raw
        elabBindersEx binders.getArgs fun xs =>
          evalEquivalenceAux probId eqvId xs lhsStx proofStx true
  | _ => throwUnsupportedSyntax

end CvxLean
