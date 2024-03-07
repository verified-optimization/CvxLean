import Mathlib.Tactic.NormNum
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Meta
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.TacticBuilder
import CvxLean.Lib.Math.Data.Array
import CvxLean.Lib.Minimization
import CvxLean.Lib.Equivalence
import CvxLean.Tactic.DCP.DCPTypes
import CvxLean.Tactic.DCP.DCPMakers
import CvxLean.Tactic.Arith.Arith

/-!
# Main DCP algorithm

This file contains the main DCP algorithm (`canonize`), it can also be used as a tactic (`dcp`).
It uses the processed atom tree from `mkProcessedAtomTree` in `CvxLean/Tactic/DCP/DCPMakers.lean` to
build the forward and backward maps and prove the four properties of a `StrongEquivalence`.
-/

namespace CvxLean

open Lean Expr Meta

namespace DCP

/-- Create the forward map (`φ`) from the forward images given by the processed atom tree. -/
def makeForwardMap (oldDomain : Expr) (xs : Array Expr) (forwardImagesNewVars : Array Expr) :
    MetaM Expr := do
  withLocalDeclD `p oldDomain fun p => do
    let prs := (← Meta.mkProjections oldDomain p).map (·.2.2)
    let forwardBody := xs ++ forwardImagesNewVars
    let forwardMap ← mkLambdaFVars #[p] <| (← foldProdMk forwardBody).replaceFVars xs prs.toArray
    trace[CvxLean.debug] "Forward map: {forwardMap}."
    check forwardMap
    trace[CvxLean.debug] "Forward map checked."

    return forwardMap

/-- Build the proof of `StrongEquivalence.phi_feasibility`. This uses the feasibility proofs. -/
def makeConstrForward (oldDomain : Expr) (xs : Array Expr) (originalConstrVars : Array LocalDecl)
    (oldProblem : Expr) (constraints : Array Expr) (isVCond : Array Bool)
    (constraintsEq : Array Expr) (feasibility : OC FeasibilityProofsTree) : MetaM Expr := do
  -- `∀ {x : D}, p.feasible x → q.feasible (φ x)`.
  withLocalDeclD `p oldDomain fun p => do
    let prs := (← Meta.mkProjections oldDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[oldProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj constraints.toList
      let hProj := (cprs h).toArray

      -- Old constraint proofs.
      let mut oldConstrProofs := #[]
      for i in [:originalConstrVars.size] do
        if not isVCond[i]! then
          oldConstrProofs := oldConstrProofs.push <|
            ← mkAppM ``Eq.mpr #[constraintsEq[i]!, mkFVar originalConstrVars[i]!.fvarId]

      -- New constraint proofs.
      let newConstrProofs := feasibility.fold #[] fun acc fs =>
          fs.fold acc Array.append

      let constrForwardBody ← foldAndIntro (oldConstrProofs ++ newConstrProofs)
      let constrForwardBody := constrForwardBody.replaceFVars
        ((originalConstrVars).map (mkFVar ·.fvarId)) hProj
      let constrForwardBody ← mkLambdaFVars #[h] constrForwardBody
      let constrForwardBody := constrForwardBody.replaceFVars xs prs.toArray
      let constrForward ← mkLambdaFVars #[p] constrForwardBody
      trace[CvxLean.debug] "φ feasibility proof: {constrForward}."
      trace[CvxLean.debug] "φ feasibility proof type: {← inferType constrForward}."
      check constrForward

      return constrForward

/-- Build a proof of `StrongEquivalence.phi_optimality`. We can actually prove equality here, using
the solution-equal-atom property from the top atom that unfolds the objective function. -/
def makeObjFunForward (oldDomain : Expr) (xs : Array Expr) (originalConstrVars : Array LocalDecl)
    (oldProblem : Expr) (constraints : Array Expr) (objFunEq : Expr) : MetaM Expr := do
  -- `∀ {x : D}, p.feasible x → q.objFun (φ x) ≤ p.objFun x`.
  withLocalDeclD `p oldDomain fun p => do
    let prs := (← Meta.mkProjections oldDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[oldProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj constraints.toList
      let hProj := (cprs h).toArray

      let objFunForward ← mkAppM ``le_of_eq #[objFunEq.replaceFVars xs prs.toArray]

      let objFunForward := objFunForward.replaceFVars
        ((originalConstrVars).map (mkFVar ·.fvarId)) hProj
      let objFunForward ← mkLambdaFVars #[h] objFunForward

      let objFunForward := objFunForward.replaceFVars xs prs.toArray
      let objFunForward ← mkLambdaFVars #[p] objFunForward
      trace[CvxLean.debug] "φ optimality proof: {objFunForward}."
      trace[CvxLean.debug] "φ optimality proof type: {← inferType objFunForward}."
      check objFunForward

      return objFunForward

/-- Create the backward map (`ψ`), which is simply a projection. -/
def makeBackwardMap (xs : Array Expr) (mkDomainFunc : Expr → MetaM Expr) : MetaM Expr := do
  let backwardBody ← foldProdMk xs
  let backwardMap ← mkDomainFunc backwardBody
  trace[CvxLean.debug] "Backward map: {backwardMap}."
  check backwardMap
  trace[CvxLean.debug] "Backward map checked."

  return backwardMap

/-- Build a proof of `StrongEquivalence.psi_feasibility`. The proofs here come from the optimality
proofs and vcondition elimination. -/
def makeConstrBackward (vcondElimMap : VCondElimMap) (newDomain : Expr) (canonProblem : Expr)
    (xs : Array Expr) (ys : Array Expr) (constrOpt : Array Expr) (canonConstrs : Array Expr)
    (newConstrs : Array Expr) (newConstrVars : Array LocalDecl) : MetaM Expr := do
  -- `∀ {x : E}, q.feasible x → p.feasible (ψ x)`.
  withLocalDeclD `p newDomain fun p => do
    let prs := (← Meta.mkProjections newDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[canonProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj (canonConstrs ++ newConstrs).toList
      let hProj := cprs h
      let mut constrBackwardProofs := #[]
      let mut filteredCounter := 0
      for i in [:constrOpt.size] do
        match vcondElimMap.find? i with
          | some p =>
              constrBackwardProofs := constrBackwardProofs.push p
          | none =>
              constrBackwardProofs := constrBackwardProofs.push <|
                mkApp constrOpt[i]! hProj.toArray[filteredCounter]!
              filteredCounter := filteredCounter + 1

      let constrBackwardBody ← foldAndIntro constrBackwardProofs
      let constrBackwardBody := constrBackwardBody.replaceFVars
        (newConstrVars.map (mkFVar ·.fvarId))
        (hProj.drop (hProj.length - newConstrVars.size)).toArray

      let constrBackwardBody := constrBackwardBody.replaceFVars (xs ++ ys) prs.toArray

      let constrBackward ← mkLambdaFVars #[p, h] constrBackwardBody
      trace[CvxLean.debug] "ψ feasibility proof: {constrBackward}."
      trace[CvxLean.debug] "ψ feasibility proof type: {← inferType constrBackward}."
      check constrBackward

      return constrBackward

/-- Build a proof of `StrongEquivalence.psi_optimality`. The proofs here come from optimality proofs
on the objective function component. -/
def makeObjFunBackward (newDomain : Expr) (canonProblem : Expr) (xs : Array Expr) (ys : Array Expr)
    (objFunOpt : Expr) (canonConstrs : Array Expr) (newConstrs : Array Expr)
    (newConstrVars : Array LocalDecl) : MetaM Expr := do
  -- `∀ {x : E}, q.feasible x → p.objFun (ψ x) ≤ q.objFun x`.
  withLocalDeclD `p newDomain fun p => do
    let prs := (← Meta.mkProjections newDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[canonProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj (canonConstrs ++ newConstrs).toList
      let hProj := cprs h
      let objFunBackwardBody := objFunOpt

      let objFunBackwardBody := objFunBackwardBody.replaceFVars
        (newConstrVars.map (mkFVar ·.fvarId))
        (hProj.drop (hProj.length - newConstrVars.size)).toArray

      let objFunBackwardBody := objFunBackwardBody.replaceFVars
        (xs ++ ys) prs.toArray

      let objFunBackward ← mkLambdaFVars #[p, h] objFunBackwardBody
      trace[CvxLean.debug] "ψ optimality proof: {objFunBackward}."
      trace[CvxLean.debug] "ψ optimality proof type: {← inferType objFunBackward}."
      check objFunBackward

      return objFunBackward

open Meta Elab Tactic

/-- Main canonization procedure. Given a minimization expression, return the canonized problem, in
conic form, and a proof of equivalence. -/
def canonize (ogProblem : MinimizationExpr) : MetaM (MinimizationExpr × Expr) := do
  let ogProblemExpr := ogProblem.toExpr
  let D := ogProblem.domain
  let R := ogProblem.codomain

  -- Get `objFun` and `constraints` without projections (e.g., `p.1 + p.2`) but rather with
  -- declared variables in `originalVarsDecls` (e.g., `x + y`).
  let (objFun, constraints, originalVarsDecls) ←
    withLambdaBody ogProblem.constraints fun p constraints => do
      let pr := (← Meta.mkProjections D p).toArray
      let originalVarsDecls ←
        withLocalDeclsD (pr.map fun (n, ty, _) => (n, fun _ => return ty))
          fun xs => xs.mapM fun x => x.fvarId!.getDecl
      withExistingLocalDecls originalVarsDecls.toList do
        let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
        let constraints ← Meta.replaceProjections constraints p.fvarId! xs
        let constraints : List (Name × Expr) ← Meta.decomposeConstraints constraints
        let constraints ← constraints.mapM (fun (n, e) => do
          return (n, ← Expr.removeMData e))
        let objFunP := ogProblem.objFun.bindingBody!.instantiate1 p
        let objFun ← Meta.replaceProjections objFunP p.fvarId! xs
        return (objFun, constraints, originalVarsDecls)

  -- Make processed atom tree.
  let pat ← mkProcessedAtomTree Curvature.Convex objFun constraints originalVarsDecls

  -- Create canonized problem and equivalence proof.
  withExistingLocalDecls pat.originalVarsDecls.toList do
    -- Original problem variables.
    let originalVars := pat.originalVarsDecls.map fun decl => mkFVar decl.fvarId

    -- Make forward map (`φ`), with properties.
    let forwardMap ← makeForwardMap D originalVars pat.forwardImagesNewVars

    let (objFunForward, constrForward) ←
      withExistingLocalDecls pat.originalConstrVars.toList do
        let objFunForward ← makeObjFunForward D originalVars pat.originalConstrVars ogProblemExpr
          (pat.constraints.toArray.map Prod.snd) pat.solEqAtom.objFun.val
        let constrForward ← makeConstrForward D originalVars pat.originalConstrVars ogProblemExpr
          (pat.constraints.toArray.map Prod.snd) pat.isVCond (pat.solEqAtom.constrs.map Tree.val)
          pat.feasibility
        return (objFunForward, constrForward)

    withExistingLocalDecls pat.newVarDecls do
      -- New variables introduced by the canonization.
      let newVars := (pat.newVarDecls.map (mkFVar ·.fvarId)).toArray

      -- Canonized variables: originalVars ⊎ newVars.
      let canonVars ← (originalVars ++ newVars).mapM fun x => do
        let decl ← x.fvarId!.getDecl
        return (decl.userName, decl.type)

      -- New domain: `D × T` where `T` is the domain of the new variables.
      let E := Meta.composeDomain canonVars.toList

      -- Function to replace variables by projections in the new domain.
      let mkDomain := fun e =>
        withLocalDeclD `p E fun p => do
          let prs := (← Meta.mkProjections E p).map (·.2.2)
          let e := Expr.replaceFVars e (originalVars ++ newVars) prs.toArray
          mkLambdaFVars #[p] e

      -- Canonize problem.
      let canonConstrs := pat.canonExprs.constrs.map Tree.val
      let canonConstrs := canonConstrs.filterIdx (fun i => ¬ pat.isVCond[i]!)
      let canonProblem : MinimizationExpr :=
        { domain := E
          codomain := R
          objFun := ← mkDomain pat.canonExprs.objFun.val
          constraints := ← mkDomain <| Meta.composeAnd (canonConstrs ++ pat.newConstrs).toList }
      let canonProblemExpr := canonProblem.toExpr

      -- Make backward map (`ψ`), with properties.
      let backwardMap ← makeBackwardMap originalVars mkDomain

      let (objFunBackward, constrBackward) ←
        withExistingLocalDecls pat.newConstrVarsArray.toList do
          let objFunBackward ← makeObjFunBackward E canonProblemExpr originalVars newVars
            pat.optimality.objFun.val canonConstrs pat.newConstrs pat.newConstrVarsArray

          let constrBackward ← makeConstrBackward pat.vcondElimMap E canonProblemExpr originalVars
            newVars (pat.optimality.constrs.map (·.val)) canonConstrs pat.newConstrs
            pat.newConstrVarsArray

          return (objFunBackward, constrBackward)

      -- Combine forward and backward maps and their properties into an equivalence witness.
      let strongEqvProof ← mkAppOptM ``Minimization.StrongEquivalence.mk
        #[D, E, R, none, ogProblemExpr, canonProblemExpr,
          -- `phi`.
          forwardMap,
          -- `psi`.
          backwardMap,
          -- `phi_feasibility`
          constrForward,
          -- `psi_feasibility`
          constrBackward,
          -- `phi_optimality`
          objFunForward,
          -- `psi_optimality`
          objFunBackward]
      let eqvProof ← mkAppM ``Minimization.Equivalence.ofStrongEquivalence #[strongEqvProof]

      return (canonProblem, eqvProof)

def dcpBuilder : EquivalenceBuilder Unit := fun eqvExpr g => g.withContext do
  let ogProblem ← eqvExpr.toMinimizationExprLHS
  let (_, eqvProof) ← canonize ogProblem
  if ! (← isDefEq (mkMVar g) eqvProof) then
    throwDCPError "failed to prove equivalence."

end DCP

namespace Tactic

open Lean.Elab Lean.Elab.Tactic

/-- Tactic to canonize a problem into DCP form. It can be used directly in an `equivalence` or
`reduction` environment. However, note, that the main use of this transformation is to solve
problems using the `solve` command. -/
syntax (name := dcp) "dcp" : tactic

@[tactic dcp]
def evalDcp : Tactic := fun stx => match stx with
  | `(tactic| dcp) => do
      DCP.dcpBuilder.toTactic
      -- saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end Tactic

end CvxLean
