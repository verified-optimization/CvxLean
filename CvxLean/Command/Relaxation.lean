import Lean
import CvxLean.Lib.Relaxation
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Relaxation
import CvxLean.Meta.TacticBuilder

namespace CvxLean

open Lean Elab Meta Tactic Term Command Minimization

/--  -/
def runRelaxationTactic (mvarId : MVarId) (stx : Syntax) : TermElabM Unit :=
  runTransformationTactic TransformationGoal.Relaxation mvarId stx

/-- Run Relaxation tactic and return both the right-hand term (`q`) and the relaxation proof, of
type `Relaxation p q`. -/
def elabRelaxationProof (lhs : Expr) (rhsName : Name) (stx : Syntax) : TermElabM (Expr × Expr) :=
  elabTransformationProof TransformationGoal.Relaxation lhs rhsName stx

syntax (name := relaxation)
  "relaxation" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

/-- Relaxation command. -/
@[command_elab «Relaxation»]
def evalRelaxation : CommandElab := fun stx => match stx with
| `(Relaxation $eqvId / $probId $declSig := $proofStx) => do
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
      let (rhs, proof) ← elabRelaxationProof lhs rhsName proofStx.raw

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
          [probId.getId])

      -- Add Relaxation proof to the environment.
      let proofTy ← inferType proof
      let proofTy ← mkForallFVars (xs.map Prod.snd) proofTy
      let proofTy ← instantiateMVars proofTy
      let proof ← mkLambdaFVars (xs.map Prod.snd) proof
      let proof ← instantiateMVars proof
      Lean.addDecl <|
        Declaration.defnDecl
          (mkDefinitionValEx eqvId.getId
          []
          proofTy
          proof
          (Lean.ReducibilityHints.regular 0)
          (DefinitionSafety.safe)
          [probId.getId])
  | _ => throwUnsupportedSyntax

end CvxLean
