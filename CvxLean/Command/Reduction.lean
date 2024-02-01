import Lean
import CvxLean.Lib.Reduction
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Reduction
import CvxLean.Meta.TacticBuilder

/-!
# The `reduction` command


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

/-- Reduction command. -/
@[command_elab «reduction»]
def evalReduction : CommandElab := fun stx => match stx with
| `(reduction $redId / $probId $declSig := $proofStx) => do
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

      let rhsName := probId.getId
      let (rhs, proof) ← elabReductionProof lhs rhsName proofStx.raw

      -- Add reduced problem to the environment.
      let rhs ← instantiateMVars rhs
      let rhs ← mkLambdaFVars (xs.map Prod.snd) rhs
      let rhs ← instantiateMVars rhs
      Lean.addDecl <|
        Declaration.defnDecl
          (mkDefinitionValEx probId.getId
          []
          (← inferType rhs)
          rhs
          (Lean.ReducibilityHints.regular 0)
          (DefinitionSafety.safe)
          [])

      -- Add reduction proof to the environment.
      let proofTy ← inferType proof
      let proofTy ← mkForallFVars (xs.map Prod.snd) proofTy
      let proofTy ← instantiateMVars proofTy
      let proof ← mkLambdaFVars (xs.map Prod.snd) proof
      let proof ← instantiateMVars proof
      Lean.addDecl <|
        Declaration.defnDecl
          (mkDefinitionValEx redId.getId
          []
          proofTy
          proof
          (Lean.ReducibilityHints.regular 0)
          (DefinitionSafety.safe)
          [])
  | _ => throwUnsupportedSyntax

end CvxLean
