import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder

namespace CvxLean

namespace Meta

open Lean Lean.Meta

/-- Given a proof of `a₀ ∧ a₁ ∧ ... ∧ aₙ`, return a proof of `aᵢ`, where
`total = n - 1`. -/
def mkAndProj (e : Expr) (i : Nat) (total : Nat) : MetaM Expr := do
  match total, i with
    | 1, 0 => return e
    | 0, _ => throwError "total too small"
    | _, 0 => return ← mkAppM ``And.left #[e]
    | total + 1, i + 1 => mkAndProj (← mkAppM ``And.right #[e]) i total

/-- Remove a redundant constraint from an optimization problem, redundant
meaning that it is implied by the other constraints. -/
def removeConstr (goal : MVarId) (id : Syntax) : MetaM (MVarId × MVarId) := do
  -- invoke `replaceConstr`, which leaves us with an MVar that we can use to define
  -- a new set of constraints. We then need to show that this set of constraints is
  -- equivalent to the old one (`eqGoal`).
  let (newConstrMVar, eqGoal, newGoal) ← replaceConstr goal

  -- Assign `newConstrMVar`.
  let target := (← goal.getDecl).type
  let goalExprs ← SolutionExpr.fromGoal goal
  let oldConstr := goalExprs.constraints
  let (i, total, erasedConstr) ←
    withLambdaBody goalExprs.constraints fun p oldConstrBody => do
      let cs ← decomposeConstraints oldConstrBody
      let i := cs.findIdx fun c => c.1 == id.getId
      if i == cs.length then
        throwError "constraint {id.getId} not found"
      let cs' := cs.eraseIdx i
      let newConstr := composeAnd $ cs'.map Prod.snd
      let newConstr ← mkLambdaFVars #[p] newConstr
      newConstrMVar.assign newConstr
      return (i, cs.length, ← mkLambdaFVars #[p] (cs.get! i).2)
  let newConstr ← instantiateMVars $ mkMVar newConstrMVar

  -- Construct a proof that the old constraints are equivalent to the old ones.
  let (extraGoal, eqProof) ←
    withLambdaBody newConstr fun p newConstrBody => do
      let (extra, newImpliesOld) ←
        withLocalDeclD `h newConstrBody fun h => do
          let l ← mkProjs (total - 1) h
          let extra ← mkFreshExprSyntheticOpaqueMVar (erasedConstr.bindingBody!.instantiate1 p)
          let l := List.append (l.take i) $ extra :: l.drop i -- TODO: use ++.
          return (extra, ← mkLambdaFVars #[h] $ ← composeAndIntro l)
      let oldConstrBody := oldConstr.bindingBody!.instantiate1 p
      let oldImpliesNew ←
        withLocalDeclD `h oldConstrBody fun h => do
          let l ← mkProjs total h
          let l := l.eraseIdx i
          mkLambdaFVars #[h] $ ← composeAndIntro l
      let eqProof ← mkPropExt (← mkAppM ``Iff.intro #[oldImpliesNew, newImpliesOld])
      return (extra, ← mkLambdaFVars #[p] eqProof)
  MVarId.assign eqGoal eqProof

  return (extraGoal.mvarId!, newGoal)

where

  /-- Given a proof `h` of `a₀ ∧ a₁ ∧ ... ∧ aₙ`, return a list of proofs of `aᵢ`. -/
  mkProjs (total : Nat) (h : Expr) : MetaM (List Expr) := do
    let mut acc := []
    for k in [:total] do
      let e ← mkAndProj h (total - k - 1) total
      acc := e :: acc
    return acc

  /-- Given a list of proofs of `aᵢ`, construct a proof of `a₁ ∧ a₂ ∧ ... ∧ aₙ`, where `total = n-1`. -/
  composeAndIntro (l : List Expr) : MetaM Expr := match l with
  | [] => return mkConst ``True
  | [e] => return e
  | List.cons e es => do
    let es ← composeAndIntro es
    let eTy ← inferType e
    let esTy ← inferType es
    return mkApp4 (mkConst ``And.intro) eTy esTy e es

end Meta

namespace Tactic

open Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := removeConstr) "remove_constr" ident : tactic

@[tactic removeConstr]
partial def evalRemoveConstr : Tactic := fun stx => match stx with
| `(tactic| remove_constr $id) => do
  let (g1, g2) ← Meta.removeConstr (← getMainGoal) id.raw
  replaceMainGoal $ [g1, g2]
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
