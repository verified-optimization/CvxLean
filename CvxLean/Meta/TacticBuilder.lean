import CvxLean.Meta.Equivalence
import CvxLean.Meta.Reduction
import CvxLean.Meta.Relaxation

namespace CvxLean

namespace Meta

open Lean Meta Elab Tactic Term Command Minimization

-- TODO: `StrongEquivalence`
inductive TransformationGoal
  | Solution | Equivalence | Reduction | Relaxation

namespace TransformationGoal

def isTransitive : TransformationGoal → Bool
  | TransformationGoal.Solution => false
  | _ => true

def fromExpr (e : Expr) : MetaM TransformationGoal := do
  if e.isAppOf `Minimization.Solution then
    return TransformationGoal.Solution
  else if e.isAppOf `Minimization.Equivalence then
    return TransformationGoal.Equivalence
  else if e.isAppOf `Minimization.Reduction then
    return TransformationGoal.Reduction
  else if e.isAppOf `Minimization.Relaxation then
    return TransformationGoal.Relaxation
  else
    throwError "Expected a `Solution`, `Equivalence`, `Reduction` or `Relaxation` goal, got {e}."

def applyTransitivity (transf : TransformationGoal) (g : MVarId) : TacticM (MVarId × MVarId) :=
  g.withContext do
    if transf.isTransitive then
      let gsTrans ←
        match transf with
          | TransformationGoal.Relaxation => evalTacticAt (← `(tactic| relaxation_trans)) g
          | TransformationGoal.Reduction => evalTacticAt (← `(tactic| reduction_trans)) g
          | TransformationGoal.Equivalence => evalTacticAt (← `(tactic| equivalence_trans)) g
          | _ => pure []
      if gsTrans.length != 4 then
        throwError "Transitivity failed."
      let mut gToChange := gsTrans[0]!
      gToChange.setTag Name.anonymous
      let gNext := gsTrans[1]!
      gNext.setTag Name.anonymous
      return (gToChange, gNext)
    else
      return (g, g)

end TransformationGoal

/-- -/
def RelaxationBuilder := RelaxationExpr → MVarId → TacticM Unit

namespace RelaxationBuilder

def toTactic (builder : RelaxationBuilder) : TacticM Unit := withMainContext do
  let transf ← TransformationGoal.fromExpr (← getMainTarget)

  -- Apply transitivity.
  let (gToChange, gNext) ← transf.applyTransitivity <| ← getMainGoal
  let mut gToChange := gToChange
  let mut gNext := gNext

  match transf with
    | TransformationGoal.Solution =>
        throwError "Relaxation tactic does not apply to `Solution`."
    | TransformationGoal.Equivalence => do
        throwError "Relaxation tactic does not apply to `Equivalence`."
    | TransformationGoal.Reduction => do
        throwError "Relaxation tactic does not apply to `Reduction`."
    | TransformationGoal.Relaxation => do
        pure ()

  -- Run builder.
  let relExpr ← RelaxationExpr.fromExpr (← gToChange.getType)
  builder relExpr gToChange

  -- Set next goal.
  gNext.setTag Name.anonymous
  setGoals [gNext]

end RelaxationBuilder

/-- -/
def ReductionBuilder := ReductionExpr → MVarId → Tactic

namespace ReductionBuilder

def toTactic (builder : ReductionBuilder) : Tactic := fun stx => do
  let transf ← TransformationGoal.fromExpr (← getMainTarget)

  -- Apply transitivity.
  let (gToChange, gNext) ← transf.applyTransitivity <| ← getMainGoal
  let mut gToChange := gToChange
  let mut gNext := gNext

  -- Convert `Solution` goal to `Reduction` goal if needed.
  match transf with
    | TransformationGoal.Solution =>
        if let [red, sol, _, _] ← gToChange.apply (mkConst ``Minimization.Reduction.toBwd) then
          -- Set the reduction as the goal to change and set the solution as the next goal.
          gToChange := red
          gNext := sol
        else
          throwError "Could not apply reduction tactic to `Solution`."
    | TransformationGoal.Equivalence => do
        throwError "Expected `Reduction`, found `Equivalence`."
    | TransformationGoal.Relaxation => do
        throwError "Expected `Reduction`, found `Relaxation`."
    | TransformationGoal.Reduction => do
        pure ()

  -- Run builder.
  let redExpr ← ReductionExpr.fromExpr (← gToChange.getType)
  builder redExpr gToChange stx

  -- Set next goal.
  gNext.instantiateMVars
  setGoals [gNext]

end ReductionBuilder

/-- -/
def EquivalenceBuilder := EquivalenceExpr → MVarId → TacticM Unit

namespace EquivalenceBuilder

def toTactic (builder : EquivalenceBuilder) : TacticM Unit := withMainContext do
  let transf ← TransformationGoal.fromExpr (← getMainTarget)

  -- Apply transitivity.
  let (gToChange, gNext) ← transf.applyTransitivity <| ← getMainGoal
  let mut gToChange := gToChange
  let mut gNext := gNext

  -- Convert reduction to equivalence if needed.
  match transf with
    | TransformationGoal.Solution =>
        if let [eqv, sol, _, _] ← gToChange.apply (mkConst ``Minimization.Equivalence.toBwd) then
          -- Set the equivalence as the goal to change and set the solution as the next goal.
          gToChange := eqv
          gNext := sol
        else
          throwError "Could not apply equivalence tactic to `Solution`."
    | TransformationGoal.Equivalence => do
        pure ()
    | TransformationGoal.Reduction => do
        if let [eqv] ← gToChange.apply (mkConst ``Minimization.Reduction.ofEquivalence) then
          gToChange := eqv
        else
          throwError "Could not apply equivalence tactic to `Reduction`."
    | TransformationGoal.Relaxation => do
        throwError "Equivalence tactic does not apply to `Relaxation`."

  -- Run builder.
  let eqvExpr ← EquivalenceExpr.fromExpr (← gToChange.getType)
  builder eqvExpr gToChange

  -- Set next goal.
  gNext.setTag Name.anonymous
  setGoals [gNext]

end EquivalenceBuilder

-- For reduction and equivalence commands.

def runTransformationTactic (transf : TransformationGoal) (mvarId : MVarId) (stx : Syntax) :
    TermElabM Unit := do
  let tacticStx := ⟨stx[1]⟩
  let rflTacticStx ←
    match transf with
      | TransformationGoal.Solution => `(tactic| skip)
      | TransformationGoal.Equivalence => `(tactic| equivalence_rfl)
      | TransformationGoal.Reduction => `(tactic| reduction_rfl)
      | TransformationGoal.Relaxation => `(tactic| relaxation_rfl)
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

/-- Wraper that works for all defined transformations, elaborating syntax into the RHS expression
and a proof of the relation with the LHS. The RHS can be named so that the metavariable displayed
in the infoview corresponds to a user-defined name. -/
def elabTransformationProof (transf : TransformationGoal) (lhs : Expr) (rhsName : Name)
    (stx : Syntax) : TermElabM (Expr × Expr) := do
  withRef stx do
    let syntheticMVarsSaved := (← get).syntheticMVars
    modify fun s => { s with syntheticMVars := {} }
    try
      -- Unfold LHS if needed.
      let lhs := ← do
        let (n, _) := lhs.getAppFnArgs
        if n != ``Minimization.mk then
          let r ← unfold lhs n
          return r.expr
        else
          return lhs

      -- Build type.
      let lhsMinExpr ← MinimizationExpr.fromExpr lhs
      let D := lhsMinExpr.domain
      let E ← Meta.mkFreshTypeMVar
      let R := lhsMinExpr.codomain
      let RPreorder ← Meta.mkFreshExprMVar (mkAppN (Lean.mkConst ``Preorder [levelZero]) #[R])
      let rhs ← Meta.mkFreshExprMVar (userName := rhsName)
        (mkAppN (Lean.mkConst ``Minimization) #[E, R])
      let transfTy :=
        match transf with
          | TransformationGoal.Solution =>
              mkAppN (mkConst ``Minimization.Solution) #[D, E, R, RPreorder, lhs]
          | TransformationGoal.Equivalence =>
              mkAppN (mkConst ``Minimization.Equivalence) #[D, E, R, RPreorder, lhs, rhs]
          | TransformationGoal.Reduction =>
              mkAppN (mkConst ``Minimization.Reduction) #[D, E, R, RPreorder, lhs, rhs]
          | TransformationGoal.Relaxation =>
              mkAppN (mkConst ``Minimization.Relaxation) #[D, E, R, RPreorder, lhs, rhs]

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
