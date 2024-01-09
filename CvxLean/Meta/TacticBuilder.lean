import CvxLean.Meta.Equivalence
import CvxLean.Meta.Reduction

namespace CvxLean

namespace Meta

open Lean Meta Elab Tactic Term Command Minimization

inductive ExpectedTransformation
  | Equivalence | Reduction

def expectedTransformationFromExpr (e : Expr) : MetaM ExpectedTransformation := do
  if e.isAppOf `Minimization.Equivalence then
    return ExpectedTransformation.Equivalence
  else if e.isAppOf `Minimization.Reduction then
    return ExpectedTransformation.Reduction
  else
    throwError "Expected an `Equivalence` or `Reduction`, got {e}."

/-- -/
def ReductionBuilder := ReductionExpr → MVarId → Tactic

namespace ReductionBuilder

def toTactic (builder : ReductionBuilder) : Tactic := fun stx => do
  match ← expectedTransformationFromExpr (← getMainTarget) with
    | ExpectedTransformation.Equivalence => do
        throwError "Expected `Reduction`, found `Equivalence`."
    | _ => do
        pure ()

  -- Apply transitivity.
  let g ← getMainGoal
  let gsTrans ← evalTacticAt (← `(tactic| reduction_trans)) g
  if gsTrans.length != 4 then
    throwError "Reduction transitivity failed."
  let gToChange := gsTrans[0]!
  let gNext := gsTrans[1]!

  -- Run builder.
  let redExpr ← ReductionExpr.fromExpr (← gToChange.getType)
  builder redExpr gToChange stx

  -- Set next goal.
  setGoals [gNext]

end ReductionBuilder

/-- -/
def EquivalenceBuilder := EquivalenceExpr → MVarId → Tactic

namespace EquivalenceBuilder

def toTactic (builder : EquivalenceBuilder) : Tactic := fun stx => do
  let transf ← expectedTransformationFromExpr (← getMainTarget)

  -- Apply transitivity.
  let g ← getMainGoal
  let gsTrans ←
    match transf with
    | ExpectedTransformation.Reduction => evalTacticAt (← `(tactic| reduction_trans)) g
    | ExpectedTransformation.Equivalence => evalTacticAt (← `(tactic| equivalence_trans)) g
  if gsTrans.length != 4 then
    throwError "Equivalence transitivity failed."
  let mut gToChange := gsTrans[0]!
  let gNext := gsTrans[1]!

  -- Convert reduciton to equivalence if needed.
  match transf with
    | ExpectedTransformation.Reduction => do
        if let [g] ← gToChange.apply (mkConst ``Minimization.Reduction.ofEquivalence) then
          gToChange := g
        else
          throwError "Could not convert equivalence tactic to reduction tactic."
    | _ => do
        pure ()

  let eqvExpr ← EquivalenceExpr.fromExpr (← gToChange.getType)
  builder eqvExpr gToChange stx

  -- Set next goal.
  setGoals [gNext]

end EquivalenceBuilder

-- For reduction and equivalence commands.

def runTransformationTactic (transf : ExpectedTransformation) (mvarId : MVarId) (stx : Syntax) :
    TermElabM Unit := do
  let tacticStx := ⟨stx[1]⟩
  let rflTacticStx ←
    match transf with
    | ExpectedTransformation.Equivalence => `(tactic| equivalence_rfl)
    | ExpectedTransformation.Reduction => `(tactic| reduction_rfl)
  let code ← `(tactic| $tacticStx <;> $rflTacticStx)

  instantiateMVarDeclMVars mvarId
  withInfoHole mvarId do
    let remainingGoals ← Tactic.run mvarId do
      withTacticInfoContext stx do
        evalTactic code

    match remainingGoals with
    | [] => pure ()
    | _ => reportUnsolvedGoals remainingGoals

    synthesizeSyntheticMVars (mayPostpone := false)

def elabTransformationProof (transf : ExpectedTransformation) (lhs : Expr) (stx : Syntax) :
    TermElabM (Expr × Expr) := do
  withRef stx do
    let syntheticMVarsSaved := (← get).syntheticMVars
    modify fun s => { s with syntheticMVars := {} }
    try
      -- Build type.
      let lhsTy ← inferType lhs
      let lhsMinExpr ← MinimizationExpr.fromExpr lhsTy
      let D := lhsMinExpr.domain
      let E ← Meta.mkFreshTypeMVar
      let R := lhsMinExpr.codomain
      let RPreorder ← Meta.mkFreshExprMVar (mkAppN (Lean.mkConst ``Preorder [levelZero]) #[R])
      let rhs ← Meta.mkFreshExprMVar (mkAppN (Lean.mkConst ``Minimization) #[E, R])
      let transfTy :=
        match transf with
          | ExpectedTransformation.Reduction =>
              mkAppN (mkConst ``Minimization.Reduction) #[D, E, R, RPreorder, lhs, rhs]
          | ExpectedTransformation.Equivalence =>
              mkAppN (mkConst ``Minimization.Equivalence) #[D, E, R, RPreorder, lhs, rhs]

      -- Proof from `stx`.
      let proof ← elabTerm stx (some transfTy)

      let some mvarDecl ← getSyntheticMVarDecl? proof.mvarId! |
        throwError "SyntheticMVarDecl not found."

      modify fun s => { s with syntheticMVars := {} }

      match mvarDecl.kind with
      | SyntheticMVarKind.tactic tacticCode savedContext =>
          withSavedContext savedContext do
            runTransformationTactic transf proof.mvarId! tacticCode
      | _ => throwError "Expected SyntheticMVarDecl of kind `tactic`, got {mvarDecl.kind}"

      return (rhs, ← instantiateMVars proof)
    finally
      modify fun s => { s with syntheticMVars :=
        s.syntheticMVars.mergeBy (fun _ _ a => a) syntheticMVarsSaved }

end Meta

end CvxLean
