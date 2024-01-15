import Lean
import CvxLean.Lib.Equivalence
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

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

def reduceExpr (e : Expr) : MetaM Expr :=
  withTransparency (mode := TransparencyMode.all) <|
    reduce e (skipProofs := false) (skipTypes := false)

def mycfg : Simp.Config := {
  zeta              := true
  beta              := true
  eta               := true
  iota              := true
  proj              := true
  decide            := true
  arith             := true
  dsimp := true
  -- autoUnfold        := true
  -- ground            := true
  etaStruct := .all
  -- contextual :=true
  maxSteps := 10000
  unfoldPartialApp := true
}

#check Std.Tactic.NormCast.evalPushCast

/-- Create `equivalence` command. It is similar to the `reduction` command, but requires an
`Equivalence` instead of a `Reduction`. -/
@[command_elab «equivalence»]
def evalEquivalence : CommandElab := fun stx => match stx with
| `(equivalence $eqvId / $probId $declSig := $proofStx) => do
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

      -- Get psi.
      let psi := (← whnf eqv).getArg! 7
      -- let psi ← reduceExpr psi
      -- let mut simpThms := {}
      -- simpThms ← simpThms.addDeclToUnfold `Eq.rec
      -- let simpCtx :=
      -- {
      --   simpTheorems  := #[simpThms]
      --   congrTheorems := (← getSimpCongrTheorems)
      --   config        := Simp.neutralConfig
      -- }
      -- lambdaTelescope (← whnf psi) <| fun xs psiXs => do
      let simpCtx ← Simp.Context.mkDefault
      let cfg : Simp.Config := default
      let mut simpCtx := { simpCtx with config := mycfg

      -- { cfg with iota := true, proj := true, eta := true, zeta := true, beta := true, contextual :=true, maxSteps := 10000 }

      }
      trace[Meta.debug] "cfg iota: {simpCtx.config.iota}"
      let mut simpThms := {}
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.psi
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.mk
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.trans
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.refl
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.rewrite_constraint_2_last
      simpThms ← simpThms.addDeclToUnfold ``Minimization.Equivalence.ofStrongEquivalence
      -- simpThms ← simpThms.addDeclToUnfold ``Eq.mpr
      -- simpThms ← simpThms.addDeclToUnfold ``Eq.ndrec
      -- simpThms ← simpThms.addDeclToUnfold ``Eq.rec
      -- simpThms ← simpThms.addDeclToUnfold ``Eq.symm
      -- simpThms ← simpThms.addDeclToUnfold ``cast
      let simpThmsArray := #[simpThms]
      simpCtx := { simpCtx with simpTheorems := simpThmsArray }
      let (res, used) ← simp psi simpCtx
      let psi := res.expr
      trace[Meta.debug] "psi: {← inferType psi}"
      trace[Meta.debug] "psi: {psi}"

  | _ => throwUnsupportedSyntax

end CvxLean
