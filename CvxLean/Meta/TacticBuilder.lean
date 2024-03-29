import CvxLean.Meta.Equivalence
import CvxLean.Meta.Reduction
import CvxLean.Meta.Relaxation
import CvxLean.Meta.Util.Error

/-!
There is a hierarchy on the possible transformations between two problems. Most crucially, a
tactic that builds an `Equivalence` should also build a `Reduction`. And both equivalence and
reduction-preserving tactics should build backward maps.

This file avoid unnecessary code duplication by providing a common interface for all
transformation-preserving tactics. When building a tactic, a user must define an
`EquivalenceBuilder`, a `ReductionBuilder` or a `RelaxationBuilder`. These builders can then be
turned into tactics using the `toTactic` method.
-/

namespace CvxLean

namespace Meta

open Lean Meta Elab Tactic Term Command Minimization

-- TODO: `StrongEquivalence`.
inductive TransformationGoal
  | Solution | Equivalence | Reduction | Relaxation

namespace TransformationGoal

def isTransitive : TransformationGoal → Bool
  | TransformationGoal.Solution => false
  | _ => true

def fromExpr (e : Expr) : MetaM TransformationGoal := do
  let e ← whnf e
  if e.isAppOf ``Minimization.Solution then
    return TransformationGoal.Solution
  else if e.isAppOf ``Minimization.Equivalence then
    return TransformationGoal.Equivalence
  else if e.isAppOf ``Minimization.Reduction then
    return TransformationGoal.Reduction
  else if e.isAppOf ``Minimization.Relaxation then
    return TransformationGoal.Relaxation
  else
    trace[Meta.TacticBuilder] "{e.ctorName}"
    throwTacticBuilderError
      "expected a `Solution`, `Equivalence`, `Reduction` or `Relaxation` goal, got {e}."

/-- Applies appropriate transitivity tactic to the goal. -/
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
        throwTacticBuilderError "transitivity failed."
      let mut gToChange := gsTrans[0]!
      gToChange.setTag Name.anonymous
      let gNext := gsTrans[1]!
      gNext.setTag Name.anonymous
      return (gToChange, gNext)
    else
      return (g, g)

end TransformationGoal

/-- Given a relaxation goal in the form of a `RelaxationExpr` and the `MVarId` of the current goal,
provide a tactic to close it. -/
def RelaxationBuilder (α) := RelaxationExpr → MVarId → TacticM α

namespace RelaxationBuilder

def toTactic {α} (builder : RelaxationBuilder α) : TacticM α := withMainContext do
  let transf ← TransformationGoal.fromExpr (← getMainTarget)

  -- Apply transitivity.
  let (gToChange, gNext) ← transf.applyTransitivity <| ← getMainGoal
  let mut gToChange := gToChange
  let mut gNext := gNext

  match transf with
    | TransformationGoal.Solution =>
        throwTacticBuilderError "relaxation tactic does not apply to `Solution`."
    | TransformationGoal.Equivalence => do
        throwTacticBuilderError "relaxation tactic does not apply to `Equivalence`."
    | TransformationGoal.Reduction => do
        throwTacticBuilderError "relaxation tactic does not apply to `Reduction`."
    | TransformationGoal.Relaxation => do
        pure ()

  -- Run builder.
  let relExpr ← RelaxationExpr.fromExpr (← gToChange.getType)
  let res ← builder relExpr gToChange

  -- Set next goal.
  gNext.setTag Name.anonymous
  setGoals [gNext]

  return res

end RelaxationBuilder

/-- Given a reduction goal in the form of a `ReductionExpr` and the `MVarId` of the current goal,
provide a tactic to close it. -/
def ReductionBuilder (α) := ReductionExpr → MVarId → TacticM α

namespace ReductionBuilder

def toTactic {α} (builder : ReductionBuilder α) : TacticM α := do
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
          throwTacticBuilderError "could not apply reduction tactic to `Solution`."
    | TransformationGoal.Equivalence => do
        throwTacticBuilderError "expected `Reduction`, found `Equivalence`."
    | TransformationGoal.Relaxation => do
        throwTacticBuilderError "expected `Reduction`, found `Relaxation`."
    | TransformationGoal.Reduction => do
        pure ()

  -- Run builder.
  let redExpr ← ReductionExpr.fromExpr (← gToChange.getType)
  let res ← builder redExpr gToChange

  -- Set next goal.
  gNext.instantiateMVars
  setGoals [gNext]

  return res

end ReductionBuilder

/-- Given an equivalence goal in the form of a `EquivalenceExpr` and the `MVarId` of the current
goal, provide a tactic to close it. -/
def EquivalenceBuilder (α) := EquivalenceExpr → MVarId → TacticM α

namespace EquivalenceBuilder

def toTactic {α} (builder : EquivalenceBuilder α) : TacticM α := withMainContext do
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
          throwTacticBuilderError "could not apply equivalence tactic to `Solution`."
    | TransformationGoal.Equivalence => do
        pure ()
    | TransformationGoal.Reduction => do
        if let [eqv] ← gToChange.apply (mkConst ``Minimization.Reduction.ofEquivalence) then
          gToChange := eqv
        else
          throwTacticBuilderError "could not apply equivalence tactic to `Reduction`."
    | TransformationGoal.Relaxation => do
        throwTacticBuilderError "equivalence tactic does not apply to `Relaxation`."

  -- Run builder.
  let eqvExpr ← EquivalenceExpr.fromExpr (← gToChange.getType)
  let res ← builder eqvExpr gToChange

  -- Set next goal.
  gNext.setTag Name.anonymous
  setGoals [gNext]

  return res

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
        throwTacticBuilderError "`SyntheticMVarDecl` not found."

      modify fun s => { s with syntheticMVars := {} }

      match mvarDecl.kind with
      | SyntheticMVarKind.tactic tacticCode savedContext =>
          withSavedContext savedContext do
            runTransformationTactic transf proof.mvarId! tacticCode
      | _ =>
          throwTacticBuilderError
            "expected `SyntheticMVarDecl` of kind `tactic`, got {mvarDecl.kind}"

      return (rhs, ← instantiateMVars proof)
    finally
      modify fun s => { s with syntheticMVars :=
        s.syntheticMVars.mergeBy (fun _ _ a => a) syntheticMVarsSaved }

end Meta

end CvxLean
