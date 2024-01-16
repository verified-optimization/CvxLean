import Lean
import CvxLean.Lib.Equivalence
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Command.Solve.Float.RealToFloat
import CvxLean.Tactic.Basic.ChangeOfVariables

namespace CvxLean

open Lean Elab Meta Tactic Term Command Minimization

/--  -/
partial def runEquivalenceTactic (mvarId : MVarId) (stx : Syntax) : TermElabM Unit := do
  runTransformationTactic TransformationGoal.Equivalence mvarId stx

/-- Run equivalence tactic and return both the right-hand term (`q`) and the equivalence proof, of
type `Equivalence p q`. -/
def elabEquivalenceProof (lhs : Expr) (stx : Syntax) : TermElabM (Expr × Expr) := do
  elabTransformationProof TransformationGoal.Equivalence lhs stx

syntax (name := equivalence)
  "equivalence" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

syntax (name := equivalenceAndBwdMap)
  "equivalence'" ident "/" ident declSig ":=" Lean.Parser.Term.byTactic : command

/-- See `evalEquivalence` and `evalEquivalenceAndBwdMap`. -/
def evalEquivalenceAux (probId eqvId: TSyntax `ident) (xs: Array (Syntax × Expr))
    (lhsStx: Syntax) (proofStx: TSyntax `Lean.Parser.Term.byTactic) (bwdMap : Bool) :
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

  let (rhs, eqv) ← elabEquivalenceProof lhs proofStx.raw

  -- Add equivalent problem to the environment.
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

  -- Add equivalence proof to the environment.
  let eqvTy ← inferType eqv
  let eqvTy ← instantiateMVars eqvTy
  let eqv ← instantiateMVars eqv
  Lean.addDecl <|
    Declaration.defnDecl
      (mkDefinitionValEx eqvId.getId
      []
      eqvTy
      eqv
      (Lean.ReducibilityHints.regular 0)
      (DefinitionSafety.safe)
      [probId.getId])

  if bwdMap then
    -- Get psi, reduce it appropriately and convert to float.
    let psi := (← whnf eqv).getArg! 7

    let mut simpCtx ← Simp.Context.mkDefault
    let simpCfg : Simp.Config :=
      { zeta             := true
        beta             := true
        eta              := true
        iota             := true
        proj             := true
        decide           := true
        arith            := true
        dsimp            := true
        unfoldPartialApp := true
        etaStruct        := .all }
    simpCtx := { simpCtx with config := simpCfg }

    let mut simpThms := {}
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.mk
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.refl
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.trans
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.ofStrongEquivalence
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.ofEq
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.psi
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.map_objFun
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.map_objFun_log
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.map_objFun_sq
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_objFun
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.map_domain
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_objFun
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraints
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_1
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_2
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_3
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_4
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_5
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_6
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_7
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_8
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_9
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_10
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_1_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_2_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_3_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_4_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_5_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_6_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_7_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_8_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_9_last
    simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_10_last
    simpThms ← simpThms.addDeclToUnfold ``CvxLean.ChangeOfVariables.toEquivalence
    simpThms ← simpThms.addDeclToUnfold ``Eq.mpr
    simpThms ← simpThms.addDeclToUnfold ``Eq.mp
    simpCtx := { simpCtx with simpTheorems := #[simpThms] }

    let (res, _) ← simp psi simpCtx
    let psi := res.expr

    try
      let psiF ← realToFloat psi
      let psiFTy ← inferType psiF
      Lean.addAndCompile <|
        Declaration.defnDecl
          (mkDefinitionValEx (eqvId.getId ++ `backward_map)
          []
          psiFTy
          psiF
          (Lean.ReducibilityHints.regular 0)
          (DefinitionSafety.safe)
          [])
    catch e =>
      trace[Meta.debug]
        "`equivalence` warning: failed to create `phi_float` - {e.toMessageData}."

/-- Create `equivalence` command. It is similar to the `reduction` command, but requires an
`Equivalence` instead of a `Reduction`. -/
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
  | `(equivalence' $eqvId / $probId $declSig := $proofStx) => do
      liftTermElabM do
        let (binders, lhsStx) := expandDeclSig declSig.raw
        elabBindersEx binders.getArgs fun xs =>
          evalEquivalenceAux probId eqvId xs lhsStx proofStx true
  | _ => throwUnsupportedSyntax


end CvxLean
