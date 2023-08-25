import Lean
import CvxLean.Lib.Equivalence
import CvxLean.Meta.Missing.Expr

namespace CvxLean

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command
open Minimization

partial def runEquivalenceTactic (mvarId : MVarId) (tacticCode : Syntax) : 
  TermElabM Unit := do
  let code := tacticCode[1]
  
  withInfoHole mvarId do
    let _remainingGoals ← Tactic.run mvarId do
      withTacticInfoContext tacticCode do
        evalTactic code

#check @MinimizationQ.mk 

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

syntax (name := equivalence) 
  "equivalence" ident "/" ident declSig ":=" term : command

@[command_elab «equivalence»]
def evalEquivalence : CommandElab := fun stx => match stx with
| `(equivalence $eqvId / $probId $declSig := $proof) => do
  liftTermElabM do
    let (binders, prob) := expandDeclSig declSig.raw
    elabBindersEx binders.getArgs fun xs => do
      let D ← Meta.mkFreshTypeMVar
      let R ← Meta.mkFreshTypeMVar
      let RPreorder ← Meta.mkFreshExprMVar
        (some <| mkAppN (Lean.mkConst ``Preorder [levelZero]) #[R])
      let prob₁Ty := mkApp2 (Lean.mkConst ``Minimization) D R
      let prob₁ ← elabTermAndSynthesizeEnsuringType prob (some prob₁Ty)
      let probQ₁ := mkAppN (Lean.mkConst ``MinimizationQ.mk) #[R, RPreorder, D, prob₁]
      let (probQ₂, proof) ← elabEquivalenceProof probQ₁ proof.raw
      let prob₂ := probQ₂.appArg!
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

lemma t1x : MinimizationQ.mk t1 = MinimizationQ.mk tx := sorry

equivalence eqv / t2 : t1 := by
  unfold t1
  have := t1x
  unfold t1 at this
  rw [this]

#check eqv
#print t2
