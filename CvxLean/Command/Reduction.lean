import Lean
import CvxLean.Lib.Minimization
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Missing.Expr

namespace CvxLean

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command
open Minimization

/-- Run the tactics written by the user. -/
partial def runReductionTactic (mvarId : MVarId) (tacticCode : Syntax) 
: TermElabM Unit := do
  -- Recall, `tacticCode` is the whole `by ...` expression.
  let code := tacticCode[1]
  instantiateMVarDeclMVars mvarId
  withInfoHole mvarId do
    let (fvarDone, mvarId) ← MVarId.intro mvarId `done
    let remainingGoals ← Tactic.run mvarId do
      withTacticInfoContext tacticCode do
        evalTactic code

    match remainingGoals with
    | [] => pure ()
    | [g] => do 
      MVarId.withContext g do
        if ← isDefEq (← inferType $ mkMVar g) (← inferType $ mkFVar fvarDone) then
          MVarId.assign g (mkFVar fvarDone)
        else
          reportUnsolvedGoals remainingGoals
    | _ => reportUnsolvedGoals remainingGoals

    synthesizeSyntheticMVars (mayPostpone := false)

/-- Run reduction tactic and add instantiate metavariables accordingly. -/
def elabReductionProof (stx : Syntax) (expectedType : Expr) : TermElabM Expr :=
  withRef stx do
    let syntheticMVarsSaved := (← get).syntheticMVars
    modify fun s => { s with syntheticMVars := {} }
    try
      let mvar ← elabTerm stx (some expectedType)
      if not mvar.isMVar then
        throwError "Expected MVar."
      let some mvarDecl ← getSyntheticMVarDecl? mvar.mvarId!
        | throwError "SyntheticMVarDecl not found."

      modify fun s => { s with syntheticMVars := {} }
      
      match mvarDecl.kind with
      | SyntheticMVarKind.tactic tacticCode savedContext =>
        withSavedContext savedContext do
          runReductionTactic mvar.mvarId! tacticCode
      | _ => throwError "Expected SyntheticMVarDecl of kind tactic."
      return ← instantiateMVars mvar
    finally
      modify fun s => { s with syntheticMVars := 
        s.syntheticMVars.mergeBy (fun _ _ a => a) syntheticMVarsSaved }

syntax (name := reduction) 
  "reduction" ident "/" ident declSig ":=" Parser.Term.byTactic : command

/-- Reduction command. -/
@[command_elab «reduction»]
def evalReduction : CommandElab := fun stx => match stx with
| `(reduction $redId / $probId $declSig := $proof) => do
  liftTermElabM do
    let (binders, prob) := expandDeclSig declSig.raw
    elabBindersEx binders.getArgs fun xs => do
      let D1 ← Meta.mkFreshTypeMVar
      let R1 ← Meta.mkFreshTypeMVar
      let D2 ← Meta.mkFreshTypeMVar
      let R2 ← Meta.mkFreshTypeMVar
      let prob₁Ty := mkApp2 (Lean.mkConst ``Minimization) D1 R1
      let prob ← elabTermAndSynthesizeEnsuringType prob (some $ prob₁Ty)
      let R2Preorder ← Meta.mkFreshExprMVar
        (some $ mkAppN (Lean.mkConst ``Preorder [levelZero]) #[R2])
      let prob₂Ty := mkAppN (Lean.mkConst ``Minimization) #[D2, R2]
      let prob₂ ← Meta.mkFreshExprMVar (some $ prob₂Ty)
      let proof ← elabReductionProof proof.raw
        (← mkArrow 
          (mkAppN (Lean.mkConst ``Solution) #[D2, R2, R2Preorder, prob₂]) 
          (← mkAppM ``Solution #[prob]))
      let prob₂ ← instantiateMVars prob₂
      let prob₂ ← mkLambdaFVars (xs.map Prod.snd) prob₂
      -- TODO: Generalize the function in Solve to add definitions inferring type.
      Lean.addDecl $ Declaration.defnDecl (mkDefinitionValEx probId.getId [] (← inferType prob₂) prob₂ (Lean.ReducibilityHints.regular 0) (DefinitionSafety.safe) [probId.getId])
      let proofTy ← instantiateMVars (← mkArrow 
          (mkAppN (Lean.mkConst ``Solution) #[D2, R2, R2Preorder, (mkAppN (Lean.mkConst probId.getId) (xs.map Prod.snd))]) 
          (← mkAppM ``Solution #[prob]))
      let proofTy ← mkForallFVars (xs.map Prod.snd) proofTy
      let proof ← mkLambdaFVars (xs.map Prod.snd) proof
      Lean.addDecl $ Declaration.defnDecl (mkDefinitionValEx redId.getId [] proofTy proof (Lean.ReducibilityHints.regular 0) (DefinitionSafety.safe) [probId.getId])
      -- TODO: Definitional height for Lean.ReducibilityHints.regular.
| _ => throwUnsupportedSyntax
