import Lean
import CvxLean.Lib.Equivalence
import CvxLean.Meta.Missing.Expr

namespace CvxLean

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command
open Minimization

/-- Simply run `tacticCode` in `mvarId`. -/
partial def runEquivalenceTactic (mvarId : MVarId) (tacticCode : Syntax) : 
  TermElabM Unit := do
  let code := tacticCode[1]
  
  withInfoHole mvarId do
    let _remainingGoals ← Tactic.run mvarId do
      withTacticInfoContext tacticCode do
        evalTactic code

/-- Run equivalence tactic and return both the right-hand term (`q`) and the 
equivalence proof, of type `Equivalence p q`. -/
def elabEquivalenceProof (prob : Expr) (stx : Syntax) : TermElabM (Expr × Expr) := do 
  withRef stx do
    let probTy ← inferType prob
    let R := probTy.getArg! 1
    let D := probTy.getArg! 0
    let E ← Meta.mkFreshTypeMVar
    let RPreorder ← Meta.mkFreshExprMVar
      (some <| mkAppN (Lean.mkConst ``Preorder [levelZero]) #[R])
    let prob₂ ← Meta.mkFreshExprMVar 
      (some <| mkApp2 (Lean.mkConst ``Minimization) E R)
    let eqvTy := mkAppN
      (mkConst ``Minimization.Equivalence) 
      #[R, D, E, RPreorder, prob, prob₂]
    let eqv ← elabTerm stx (some eqvTy)

    let some mvarDecl ← getSyntheticMVarDecl? eqv.mvarId! | throwError "SyntheticMVarDecl not found."
    
    match mvarDecl.kind with
    | SyntheticMVarKind.tactic tacticCode savedContext =>
      withSavedContext savedContext do
        runEquivalenceTactic eqv.mvarId! tacticCode
    | _ => throwError "Expected SyntheticMVarDecl of kind tactic, got {mvarDecl.kind}"

    let eqvWitness ← instantiateMVars eqv
    let eqvWitnessTy ← inferType eqvWitness
    if eqvWitnessTy.isAppOf ``Minimization.Equivalence then 
      -- NOTE(RFM): Equivalence 0:R 1:D 2:E 3:RPreorder 4:p 5:q 
      let rhs := eqvWitnessTy.getArg! 5
      return (rhs, ← instantiateMVars eqv)
    else 
      throwError "Expected equivalence witness, got {eqvWitness}."

syntax (name := equivalence) 
  "equivalence" ident "/" ident declSig ":=" term : command

/-- Create `equivalence` command. It is similar to the `reduction` command, but
it is more strict as it requires the target and goal problem to be strongly 
equivalent, instead of simply building a map from solution spaces. -/
@[command_elab «equivalence»]
def evalEquivalence : CommandElab := fun stx => match stx with
| `(equivalence $eqvId / $probId $declSig := $proof) => do
  liftTermElabM do
    let (binders, prob) := expandDeclSig declSig.raw
    elabBindersEx binders.getArgs fun xs => do
      let D ← Meta.mkFreshTypeMVar
      let R ← Meta.mkFreshTypeMVar
      let prob₁Ty := mkApp2 (Lean.mkConst ``Minimization) D R
      let prob₁ ← elabTermAndSynthesizeEnsuringType prob (some prob₁Ty)
      dbg_trace "prob₁: {prob₁}"
      -- let probQ₁ := mkAppN (Lean.mkConst ``Minimization.mk) #[D, R, prob₁]
      -- NOTE: `instantiateMVars` does not infer the preorder instance.
      for mvarId in ← getMVars prob₁ do 
        try {
          let mvarVal ← synthInstance (← mvarId.getDecl).type
          mvarId.assign mvarVal }
        catch _ => pure ()
      
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

def p : Minimization ℕ ℕ := sorry
def q : Minimization ℕ ℕ := sorry

def x : Equivalence p q := sorry

equivalence eq / q : p := by
  exact x

#check eq.phi 

end CvxLean 
