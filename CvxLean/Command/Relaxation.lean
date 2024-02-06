import Lean
import CvxLean.Lib.Relaxation
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Relaxation
import CvxLean.Meta.TacticBuilder

/-!
# The `relaxation` command

Given a problem `p : Minimization D R` and fresh identifiers `rel` and `q`, a user can use the
relaxation command as follows:
```
relaxation rel/q : p := by ...
```
Placing the cursor on after the `by` keyword opens up a tactic environment where the goal is to
prove `p ≽' ?q`. After applying a sequence of tactics that transform the goal into, say `r ≽' ?q`,
the user can leave the relaxation environment and two new definitions will be added to the
environment:
* `q := r`,
* `rel : p ≽' q`.

This command is very similar to `equivalence` (`CvxLean/Command/Equivalence.lean`) and `reduction`
(`CvxLean/Command/Reduction.lean`) in how it is designed. Of course, the key difference is that the
goal is to prove a relaxation. Note that in this case, there is no option to create a backward map
as relaxations do not guarantee that the solution can be mapped back.
-/

namespace CvxLean

open Lean Elab Meta Tactic Term Command Minimization

/-- Run a transformation tactic indicating that a relaxation is expected. -/
def runRelaxationTactic (mvarId : MVarId) (stx : Syntax) : TermElabM Unit :=
  runTransformationTactic TransformationGoal.Relaxation mvarId stx

/-- Run relaxation tactic and return both the right-hand term (`q`) and the relaxation proof, of
type `Relaxation p q`. -/
def elabRelaxationProof (lhs : Expr) (rhsName : Name) (stx : Syntax) : TermElabM (Expr × Expr) :=
  elabTransformationProof TransformationGoal.Relaxation lhs rhsName stx

/-- Open a relaxation environment. -/
syntax (name := relaxation)
  "relaxation" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

/-- Definition of the `relaxation` command. -/
@[command_elab «relaxation»]
def evalRelaxation : CommandElab := fun stx => match stx with
| `(relaxation $relIdStx / $probIdStx $declSig := $proofStx) => do
  liftTermElabM do
    let (binders, lhsStx) := expandDeclSig declSig.raw
    elabBindersEx binders.getArgs fun xs => do
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
      let (rhs, proof) ← elabRelaxationProof lhs rhsName proofStx.raw

      -- Names for new definitions.
      let currNamespace ← getCurrNamespace
      let probId := currNamespace ++ probIdStx.getId
      let relId := currNamespace ++ relIdStx.getId

      -- Add relaxed problem to the environment.
      let rhs ← instantiateMVars rhs
      let rhs ← mkLambdaFVars (xs.map Prod.snd) rhs
      let rhs ← instantiateMVars rhs
      simpleAddDefn probId rhs

      -- Add Relaxation proof to the environment.
      let proof ← mkLambdaFVars (xs.map Prod.snd) proof
      let proof ← instantiateMVars proof
      simpleAddDefn relId proof
  | _ => throwUnsupportedSyntax

end CvxLean
