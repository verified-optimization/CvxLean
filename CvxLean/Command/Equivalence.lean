import Lean
import CvxLean.Lib.Equivalence
import CvxLean.Meta.Missing.Expr

namespace CvxLean

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command
open Minimization

syntax (name := equivalence) 
  "equivalence" ident "/" ident declSig ":=" term : command

partial def runEquivalenceTactic (mvarId : MVarId) (tacticCode : Syntax) : 
  TermElabM Unit := do
  let code := tacticCode[1]
  
  -- instantiateMVarDeclMVars mvarId
  withInfoHole mvarId do
    let remainingGoals ← Tactic.run mvarId do
      withTacticInfoContext tacticCode do
        evalTactic code

    match remainingGoals with
    | [] => pure ()
    | [g] => do 
      MVarId.withContext g do
        reportUnsolvedGoals remainingGoals
    | _ => reportUnsolvedGoals remainingGoals

    -- synthesizeSyntheticMVars (mayPostpone := false)

def elabEquivalenceProof (prob : Expr) (stx : Syntax) : TermElabM (Expr × Expr) := do 
  withRef stx do
    let eqTy ← mkEq prob (← mkFreshExprMVar none)
    let eq ← elabTerm stx (some eqTy)

    let some mvarDecl ← getSyntheticMVarDecl? eq.mvarId! | throwError "SyntheticMVarDecl not found."
    
    match mvarDecl.kind with
    | SyntheticMVarKind.tactic tacticCode savedContext =>
      withSavedContext savedContext do
        runEquivalenceTactic eq.mvarId! tacticCode
    | _ => throwError "Expected SyntheticMVarDecl of kind tactic, got {mvarDecl.kind}"
    
    let eqProof ← instantiateMVars eq
    if let some (_, _, rhs) ← matchEq? (← inferType eqProof) then 
      return (rhs, ← instantiateMVars eq)
    else 
      throwError "Expected equality proof, got {eqProof}."

@[command_elab «equivalence»]
def evalEquivalence : CommandElab := fun stx => match stx with
| `(equivalence $eqvId / $probId $declSig := $proof) => do
  liftTermElabM do
    let (binders, prob) := expandDeclSig declSig.raw
    elabBindersEx binders.getArgs fun xs => do
      let D ← Meta.mkFreshTypeMVar
      let R ← Meta.mkFreshTypeMVar
      let prob₁Ty := mkApp2 (Lean.mkConst ``Minimization) D R
      let prob₁ ← elabTermAndSynthesizeEnsuringType prob (some $ prob₁Ty)
      let (prob₂, proof) ← elabEquivalenceProof prob₁ proof.raw
      let prob₂ ← instantiateMVars prob₂
      let prob₂ ← mkLambdaFVars (xs.map Prod.snd) prob₂
      Lean.addDecl <| 
        Declaration.defnDecl 
        (mkDefinitionValEx probId.getId 
        [] 
        (← inferType prob₂) 
        prob₂ 
        (Lean.ReducibilityHints.regular 0) 
        (DefinitionSafety.safe) 
        [probId.getId])
      let proofTy ← inferType proof
      let proofTy ← mkForallFVars (xs.map Prod.snd) proofTy
      let proof ← mkLambdaFVars (xs.map Prod.snd) proof
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

def t1 := @Minimization.mk ℝ ℝ (fun x => x) (fun _ => True)

def tx := @Minimization.mk ℝ ℝ (fun x => x) (fun _ => True)

lemma t1x : t1 = tx := sorry

equivalence eqv / t2 : t1 := by
  unfold t1
  have := t1x
  unfold t1 at this
  rw [this]

#check eqv
#print t2

