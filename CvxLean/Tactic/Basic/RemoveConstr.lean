import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Expr

namespace CvxLean

open Lean Expr Meta Elab Term Tactic

namespace Meta

/-- Given a proof of `a₀ ∧ a₁ ∧ ... ∧ aₙ`, return a proof of `aᵢ`, where `total = n - 1`. -/
def mkAndProj (e : Expr) (i : Nat) (total : Nat) : MetaM Expr := do
  match total, i with
    | 1, 0 => return e
    | 0, _ => throwError "total too small"
    | _, 0 => return ← mkAppM ``And.left #[e]
    | total + 1, i + 1 => mkAndProj (← mkAppM ``And.right #[e]) i total

/-- Given a proof `h` of `a₀ ∧ a₁ ∧ ... ∧ aₙ`, return a list of proofs of `aᵢ`. -/
def mkProjs (total : Nat) (h : Expr) : MetaM (List Expr) := do
  let mut acc := []
  for k in [:total] do
    let e ← mkAndProj h (total - k - 1) total
    acc := e :: acc
  return acc

/-- Given a list of proofs of `aᵢ`, construct a proof of `a₁ ∧ a₂ ∧ ... ∧ aₙ`, where `total = n-1`.
-/
def composeAndIntro (l : List Expr) : MetaM Expr :=
  match l with
    | [] => return mkConst ``trivial
    | [e] => return e
    | List.cons e es => do
      let es ← composeAndIntro es
      let eTy ← inferType e
      let esTy ← inferType es
      return mkApp4 (mkConst ``And.intro) eTy esTy e es

/-- -/
def removeConstrBuilder (id : Name) (proof : Syntax) : EquivalenceBuilder Unit := fun eqvExpr g =>
  g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let (idxToRemove, numConstrs, newConstrs, toShow) ←
      withLambdaBody lhsMinExpr.constraints fun p oldConstrsBody => do
        let oldConstrsList ← decomposeConstraints oldConstrsBody
        let idxToRemove := oldConstrsList.findIdx fun c => c.1 == id
        if idxToRemove == oldConstrsList.length then
          throwError "`remove_constr` error: constraint {id} not found."
        let newConstrsList := oldConstrsList.eraseIdx idxToRemove
        let newConstrs ← mkLambdaFVars #[p] <| composeAnd <| newConstrsList.map Prod.snd
        -- Use `proof`. Some work is neeed to make the context look nice for the user.
        let lhsLabeledDomain ← decomposeDomain lhsMinExpr.domain
        let toShow ← withLocalDeclsDNondep lhsLabeledDomain.toArray fun xs => do
          mkLambdaFVars xs <| ← do
            let niceNewConstrsList ← newConstrsList.mapM (fun (n, c) => do
              return (n, ← replaceProjections c p.fvarId! xs))
            let toErase := (oldConstrsList.get! idxToRemove).2;
            let niceToErase ← Meta.replaceProjections toErase p.fvarId! xs
            withLocalDeclsDNondep niceNewConstrsList.toArray fun cs => do
              let (e, _) ← Lean.Elab.Term.TermElabM.run <| Lean.Elab.Term.commitIfNoErrors? <| do
                let v ← Lean.Elab.Term.elabTerm proof niceToErase
                Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
                instantiateMVars v
              if let some e' := e then
                mkLambdaFVars cs e'
              else
                throwError "`remove_constr` error: failed to elaborate proof."
        return (idxToRemove, oldConstrsList.length, newConstrs, toShow)

    -- Return iff proof and the extra goal of type `c₁ ∧ ... ∧ cᵢ₋₁ ∧ cᵢ₊₁ ∧ ... ∧ cₙ → cᵢ`.
    let iffProof ← withLambdaBody newConstrs fun p newConstrsBody => do
      -- `c₁ ∧ ... ∧ cᵢ₋₁ ∧ cᵢ₊₁ ∧ ... ∧ cₙ → c₁ ∧ ... ∧ cₙ`.
      let newImpliesOld ← withLocalDeclD `h newConstrsBody fun h => do
        let l ← mkProjs (numConstrs - 1) h
        let xs := (← mkProjections lhsMinExpr.domain p).map (fun (_, _, e) => e)
        let extra := mkAppNBeta toShow ((xs ++ l).toArray)
        let l := (l.take idxToRemove).append <| extra :: l.drop idxToRemove
        return ← mkLambdaFVars #[h] <| ← composeAndIntro l
      -- `c₁ ∧ ... ∧ cₙ → c₁ ∧ ... ∧ cᵢ₋₁ ∧ cᵢ₊₁ ∧ ... ∧ cₙ`.
      let oldConstrsBody := lhsMinExpr.constraints.bindingBody!.instantiate1 p
      let oldImpliesNew ← withLocalDeclD `h oldConstrsBody fun h => do
        let l ← mkProjs numConstrs h
        let l := l.eraseIdx idxToRemove
        mkLambdaFVars #[h] <| ← composeAndIntro l
      return ← mkLambdaFVars #[p] <| ← mkAppM ``Iff.intro #[oldImpliesNew, newImpliesOld]

    -- Prove by rewriting.
    let D := eqvExpr.domainLHS
    let R := eqvExpr.codomain
    let RPreorder := eqvExpr.codomainPreorder
    let fullProof ← mkAppOptM ``Minimization.Equivalence.rewrite_constraints
      #[D, R, RPreorder, lhsMinExpr.objFun, lhsMinExpr.constraints, newConstrs, iffProof]
    check fullProof
    let rhs := { lhsMinExpr with constraints := newConstrs }
    if !(← isDefEq eqvExpr.rhs rhs.toExpr) then
      throwError "`remove_constr` error: failed to unify RHS."

    if let _ :: _ ← g.apply fullProof then
      throwError "`remove_constr` error: failed to prove equivalence."

    let gs ← getUnsolvedGoals
    if gs.length != 0 then
      throwError "`remove_constr` error: failed to close all goals."

end Meta

namespace Tactic

/-- -/
syntax (name := removeConstr) "remove_constr" ident " => " tacticSeq : tactic

@[tactic removeConstr]
partial def evalRemoveConstr : Tactic := fun stx => match stx with
| `(tactic| remove_constr $id => $tacStx) => do
    (removeConstrBuilder id.getId (← `(term| by $tacStx))).toTactic
    saveTacticInfoForToken stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
