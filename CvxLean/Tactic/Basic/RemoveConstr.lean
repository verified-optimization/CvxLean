import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Expr

namespace CvxLean

open Lean Meta Elab Term Tactic

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

/-- Given a list of proofs of `aᵢ`, construct a proof of `a₁ ∧ a₂ ∧ ... ∧ aₙ`, where `total = n-1`. -/
def composeAndIntro (l : List Expr) : MetaM Expr :=
  match l with
    | [] => return mkConst ``True
    | [e] => return e
    | List.cons e es => do
      let es ← composeAndIntro es
      let eTy ← inferType e
      let esTy ← inferType es
      return mkApp4 (mkConst ``And.intro) eTy esTy e es

/-- -/
def removeConstrBuilder (id : Name) (proof : Syntax) : EquivalenceBuilder := fun
  eqvExpr g _ => g.withContext do
    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let (idxToRemove, numConstrs, newConstrs, toShow) ←
      withLambdaBody lhsMinExpr.constraints fun p oldConstrsBody => do
        let cs ← decomposeConstraints oldConstrsBody
        let i := cs.findIdx fun c => c.1 == id
        if i == cs.length then
          throwError "`remove_constr` error: constraint {id} not found."
        let cs' := cs.eraseIdx i
        let newConstrs ← mkLambdaFVars #[p] <| composeAnd <| cs'.map Prod.snd
        -- Use `proof`. Some work is neeed to make the context look nice for the user.
        let toShow ← mkLambdaFVars #[p] <| ← withDomainLocalDecls lhsMinExpr.domain p fun xs _ => do
          let cs' ← cs'.mapM (fun (n, c) => do
            return (n, ← Meta.replaceProjections c p.fvarId! xs))
          let toErase ← Meta.replaceProjections ((cs.get! i).2) p.fvarId! xs
          withLocalDeclsDNondep cs'.toArray fun csVars' => do
            mkLambdaFVars csVars' (← Term.elabTerm proof toErase)

        return (i, cs.length, newConstrs, toShow)

    -- Return iff proof and the extra goal of type `c₁ ∧ ... ∧ cᵢ₋₁ ∧ cᵢ₊₁ ∧ ... ∧ cₙ → cᵢ`.
    let iffProof ← withLambdaBody newConstrs fun p newConstrsBody => do
      -- `c₁ ∧ ... ∧ cᵢ₋₁ ∧ cᵢ₊₁ ∧ ... ∧ cₙ → c₁ ∧ ... ∧ cₙ`.
      let newImpliesOld ← withLocalDeclD `h newConstrsBody fun h => do
        let l ← mkProjs (numConstrs - 1) h
        let extra := mkAppNBeta toShow ((p :: l).toArray)
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
    trace[Meta.debug] "iffProof: {← inferType iffProof}"
    let D := eqvExpr.domainP
    let R := eqvExpr.codomain
    let RPreorder := eqvExpr.codomainPreorder
    let toApply ← mkAppOptM ``Minimization.Equivalence.rewrite_constraints
      #[D, R, RPreorder, lhsMinExpr.objFun, none, none, iffProof]
    let _ ← g.apply toApply
    let gs ← getUnsolvedGoals
    if gs.length != 0 then
      throwError "`remove_constr` error: failed to close goal."

end Meta

namespace Tactic

syntax (name := removeConstr) "remove_constr" ident term : tactic

@[tactic removeConstr]
partial def evalRemoveConstr : Tactic := fun stx => match stx with
| `(tactic| remove_constr $id $proof) => do
    (removeConstrBuilder id.getId proof).toTactic stx
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
