import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Meta
import CvxLean.Meta.Util.Error
import CvxLean.Tactic.DCP.AtomCurvRule
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Tactic.DCP.AtomCmdElab
import CvxLean.Tactic.DCP.DCP

/-!
# Support for multi-level atom declarations

This file defines the method `canonAtomData` which allows atom declarations to not be in conic form,
as long as they can be canonized into conic using the existing atoms at that point. This allows for
more readable atom declarations.

Note that this means that what is written after `declare_atom` is not necessarily what is stored in
the atom library, since the atom declaration might need to be canonized into conic form.
-/

namespace CvxLean

open Lean Meta Elab Expr

section Helpers

/-- Count the number of arguments with non-trivial monotonicities. -/
def getMonoArgsCount (curv : Curvature) (argKinds : Array ArgKind) : Nat :=
  argKinds.foldl (fun acc argKind =>
    match curvatureInArg curv argKind with
      | Curvature.Concave => 1 + acc
      | Curvature.Convex => 1 + acc
      | _ => acc) 0

end Helpers

section MultiLevel

/-- Use the DCP procedure on the optimization problem represented by the graph implementation. This
is the first step, we only have a raw processed atom tree at this point. -/
def processGraphImplementation (objCurv : Curvature) (atomData : GraphAtomData) (xs : Array Expr) :
    MetaM (DCP.ProcessedAtomTree × Array LocalDecl) := do
  -- First, we set up the optimization problem corresponding to the graph implementation as
  -- follows. The objective function corresponds to the implementation objective, the
  -- constraints correspond to the implmenetation constraints, and the optimization variables
  -- correspond to the implementation variables.
  let (objFun, constraints, originalVarsDecls) ← do
    let impVars := atomData.impVars.map fun (n, ty) => (n, mkAppNBeta ty xs)
    withLocalDeclsDNondep impVars fun vs => do
        let vsDecls ← vs.mapM fun v => v.fvarId!.getDecl
        let bconds := atomData.bconds.map fun (n,c) => (n, mkAppNBeta c xs)
        withLocalDeclsDNondep bconds fun bs => do
          let originalVarsDecls := vsDecls
          let objFun := mkAppNBeta atomData.impObjFun (xs ++ vs)
          let constraints := atomData.impConstrs.map (`_, mkAppNBeta · (xs ++ bs ++ vs))
          return (objFun, constraints, originalVarsDecls)

  -- Thge atom arguments are not optimization variables, but still need to be seen as affine
  -- expressions by the DCP procedure. Here, we collect all the non-constant arguments as the
  -- free variable expressions that may appear in the graph implementation.
  let xsAffPre := xs.map fun x => x.fvarId!
  let mut xsAff := #[]
  for i in [:xs.size] do
    if atomData.argKinds[i]! != ArgKind.Constant then
      xsAff := xsAff.push xsAffPre[i]!

  -- This is the key step where we ask the DCP procedure to canonize the optimization problem
  -- corresponding to the graph implementation. We indicate that the some variables coming from
  -- the atom arguments might be affine. We also include the background conditions, which may
  -- be needed to canonize the problem.
  let bconds := atomData.bconds.map fun (n,c) => (n, mkAppNBeta c xs)
  let pat ← withLocalDeclsDNondep bconds fun bs => do
    let bcondsDecls ← bs.mapM (·.fvarId!.getDecl)
    DCP.mkProcessedAtomTree objCurv objFun constraints.toList originalVarsDecls
      (extraVars := xsAff) (extraDecls := bcondsDecls)

  -- We return the result from DCP, and the optimization variables (as local declarations), which,
  -- recall, are the implementation variables.
  return (pat, originalVarsDecls)

/-- The second step is, given the processed atom tree and the raw atom data, we need to adjust all
the fields and proofs. -/
def adjustCanonAtomData (objCurv : Curvature) (atomData : GraphAtomData)
    (pat : DCP.ProcessedAtomTree) (originalVarsDecls : Array LocalDecl) (xs : Array Expr) :
    MetaM GraphAtomData := do
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls pat.newVarDecls do
      withExistingLocalDecls pat.newConstrVarsArray.toList do
        -- `vs` are the variables already present in the uncanonized graph implementation, i.e.,
        -- explicitly written by the user in the atom declaration.
        let vs := originalVarsDecls.map (mkFVar ·.fvarId)

        -- `zs` are the implementation variables to be added that come from the canonization of
        -- the atom declaration iteself.
        let zs := pat.newVarDecls.toArray.map (mkFVar ·.fvarId)

        -- Uncanonized atom conditions.
        let vconds := atomData.vconds.map fun (n,c) => (n, mkAppNBeta c xs)
        let bconds := atomData.bconds.map fun (n,c) => (n, mkAppNBeta c xs)

        /- 1. Adjust the implementation variables, essentially (`vs` and `zs`). -/

        let adjustedImpVars := atomData.impVars.append (← pat.newVarDecls.toArray.mapM
          fun decl => do return (decl.userName, ← mkLambdaFVars xs decl.type))

        trace[CvxLean.debug] "adjustedImpVars: {adjustedImpVars}"

        /- 2. Adjust the implementation objective. -/

        let adjustedImpObjFun ← mkLambdaFVars (xs ++ vs ++ zs) pat.canonExprs.objFun.val

        trace[CvxLean.debug] "adjustedImpObjFun: {adjustedImpObjFun}"

        /- 3. Adjust the implementation constraints. -/

        -- Canonized implementation constraints (in conic form), filter out those marked as
        -- vconds.
        let canonConstrs := pat.canonExprs.constrs.map Tree.val |>.filterIdx
          (fun i => !pat.isVCond[i]!)

        -- DCP might have also added new constraints.
        let newConstrs := pat.newConstrs

        -- The adjusted constraints need to take into account the `zs`. Recall that implementation
        -- constraints may also use background conditions.
        let adjustedImpConstrs ← (canonConstrs ++ newConstrs).mapM (fun c => do
          withLocalDeclsDNondep bconds fun as => mkLambdaFVars (xs ++ as ++ vs ++ zs) c)

        trace[CvxLean.debug] "adjustedImpConstrs: {adjustedImpConstrs}"

        /- 4. Adjust the solution. -/

        -- Solutions to `vs` (in terms of `xs`).
        let vsSol := atomData.solution.map fun s => mkAppNBeta s xs

        -- Substitute into the canonization forward map the solutions to `vs`, which gives us the
        -- solutions of `zs` as expressions in `xs`.
        let zsSolInTermsOfXs ← pat.forwardImagesNewVars.mapM (fun e => mkLambdaFVars xs
          (e.replaceFVars vs vsSol))

        -- The adjusted solutions, are the solutions to both `vs` abd `zs` as expressions in `xs`.
        let adjustedSolution := vsSol ++ zsSolInTermsOfXs

        trace[CvxLean.debug] "adjustedSolution: {adjustedSolution}"

        /- 5. Adjust the feasibility proofs. -/

        let solEqAtomProofs := pat.solEqAtom.constrs.map Tree.val

        -- First, we change all the existing feasibility proofs to take into account the solutions
        -- for `zs`.
        let mut oldFeasibilityAdjusted := #[]
        for i in [:atomData.feasibility.size] do
          let feas := atomData.feasibility[i]!
          let feasXs := mkAppNBeta feas xs
          let adjustedFeas ←
            withLocalDeclsDNondep vconds fun cs => do
              withLocalDeclsDNondep bconds fun bs => do
                let feasXsVconds := mkAppNBeta feasXs cs
                let feasXsConds := mkAppNBeta feasXsVconds bs
                let proofAdjusted := solEqAtomProofs[i]!.replaceFVars vs vsSol
                let adjustedFeas ← mkAppM ``Eq.mpr #[proofAdjusted, feasXsConds]
                mkLambdaFVars (xs ++ cs ++ bs) adjustedFeas
          oldFeasibilityAdjusted := oldFeasibilityAdjusted.push adjustedFeas

        -- The new feasibility proofs are in terms of `vs` so we need to replace them by their
        -- solutions.
        let newConstrProofs := pat.feasibility.fold #[] fun acc fs => fs.fold acc Array.append
        let newFeasibility ← newConstrProofs.mapM (fun e =>
          withLocalDeclsDNondep vconds fun cs => do
            withLocalDeclsDNondep bconds fun bs => do
              mkLambdaFVars (xs ++ cs ++ bs) (e.replaceFVars vs vsSol))

        let adjustedFeasibility := oldFeasibilityAdjusted ++ newFeasibility

        trace[CvxLean.debug] "adjustedFeasibility: {adjustedFeasibility}"

        /- 6. Adjust the optimality proof. -/

        let constrsOptimalityProofs := pat.optimality.constrs.map Tree.val
        let objFunOptimalityProof := pat.optimality.objFun.val
        let adjustedOptimality ←
          withLocalDeclsDNondep bconds fun bs => do
            -- Apply variables, background conditions, and implementation variables to the
            -- user-provided optimality proof.
            let optimalityXsBConds := mkAppN atomData.optimality (xs ++ bs ++ vs)
            withLocalDeclsDNondep (canonConstrs.map (fun rc => (`_, rc))) fun cs => do
              -- Then, apply all constraints.
              let mut optimalityAfterCanon := optimalityXsBConds
              for i in [:canonConstrs.size] do
                let c := mkApp constrsOptimalityProofs[i]! cs[i]!
                optimalityAfterCanon := mkApp optimalityAfterCanon c
              -- At this point, we have the monotonicity conditions implying the optimality
              -- condition.
              -- Then, adjust the condition using `objFunOptimalityProof`. We need to deal with
              -- the monotonicity conditions carefully as well.
              let monoArgsCount := getMonoArgsCount objCurv atomData.argKinds
              let optCondAdjusted ←
                lambdaTelescope (← whnf optimalityAfterCanon) <| fun optArgs e => do
                -- Every extra argument has an extra condition, e.g. x', x ≤ x.
                let monoArgs := optArgs[:2 * monoArgsCount]
                let optCondition ← mkLambdaFVars optArgs[2 * monoArgsCount:] e
                let atomRange ← inferType (mkAppNBeta atomData.expr xs)
                -- Obtain the new condition by transitivty.
                let newCond ←
                  if atomData.curvature == Curvature.Convex then
                    mkAppOptM ``le_trans #[
                      atomRange, none, none, none, none,
                      optCondition, objFunOptimalityProof]
                  else
                    mkAppOptM ``le_trans #[
                      atomRange, none, none, none, none,
                      objFunOptimalityProof, optCondition]
                mkLambdaFVars monoArgs newCond

              let ds := pat.newConstrVarsArray.map (mkFVar ·.fvarId)
              mkLambdaFVars (xs ++ bs ++ vs ++ zs ++ cs ++ ds) optCondAdjusted

        trace[CvxLean.debug] "adjustedOptimality: {adjustedOptimality}"

        /- 7. Adjust vconditionElimination -/

        let mut adjustedVCondElim := #[]
        for vcondElim in atomData.vcondElim do
          let newVCondElim := mkAppN vcondElim (xs ++ vs)
          let newVCondElim ←
            withLocalDeclsDNondep (canonConstrs.map (fun rc => (`_, rc))) fun cs => do
              let mut newVCondElim := newVCondElim
              for i in [:canonConstrs.size] do
                let c := mkApp constrsOptimalityProofs[i]! cs[i]!
                newVCondElim := mkApp newVCondElim c
              let ds := pat.newConstrVarsArray.map (mkFVar ·.fvarId)
              mkLambdaFVars (xs ++ vs ++ zs ++ cs ++ ds) newVCondElim
          adjustedVCondElim := adjustedVCondElim.push newVCondElim

        trace[CvxLean.debug] "adjustedVCondElim: {adjustedVCondElim}"

        /- 8. Return the adjusted atom data. -/

        return { atomData with
          impVars := adjustedImpVars
          impObjFun := adjustedImpObjFun
          impConstrs := adjustedImpConstrs
          solution := adjustedSolution
          feasibility := adjustedFeasibility
          optimality := adjustedOptimality
          vcondElim := adjustedVCondElim
        }

/-- Given raw atom data as defined in the user (which might not be in conic form), generate new atom
data in conic form. This function calls `processGraphImplementation` to apply DCP on the
optimization problem represented by the atom's implementation and `adjustCanonAtomData` to fix all
the atom data, including the proofs. -/
def canonAtomData (objCurv : Curvature) (atomData : GraphAtomData) : MetaM GraphAtomData := do
  -- `xs` are the arguments of the atom.
  lambdaTelescope atomData.expr fun xs _ => do
    let (pat, originalVarsDecls) ← processGraphImplementation objCurv atomData xs
    adjustCanonAtomData objCurv atomData pat originalVarsDecls xs

end MultiLevel

end CvxLean
