import CvxLean.Tactic.DCP.AtomCurvRule
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Tactic.DCP.AtomCmdElab

namespace CvxLean

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

/-- Use the DCP procedure to canon the graph implementation to a problem that uses only cone
constraints and affine atoms. -/
def canonAtomData (objCurv : Curvature) (atomData : GraphAtomData) : CommandElabM GraphAtomData := do
  liftTermElabM do
    -- `xs` are the arguments of the atom.
    lambdaTelescope atomData.expr fun xs atomExpr => do
      let atomRange ← inferType atomExpr

      -- Call DCP on graph implementation.
      let (objFun, constraints, originalVarsDecls) ← do
        let impVars := atomData.impVars.map fun (n, ty) => (n, mkAppNBeta ty xs)
        withLocalDeclsDNondep impVars fun vs => do
            let vsDecls ← vs.mapM fun v => v.fvarId!.getDecl
            let bconds := atomData.bconds.map fun (n,c) => (n, mkAppNBeta c xs)
            withLocalDeclsDNondep bconds fun bs => do
              let originalVarsDecls := vsDecls
              let objFun := mkAppNBeta (mkAppNBeta atomData.impObjFun xs) vs
              trace[Meta.debug] "{xs} {bs} {vs}"
              let constraints := atomData.impConstrs.map
                fun c => (`_, mkAppNBeta (mkAppNBeta (mkAppNBeta c xs) bs) vs)
              trace[Meta.debug] "constraints in with: {constraints}"
              return (objFun, constraints, originalVarsDecls)

      let xsVarsPre := xs.map fun x => x.fvarId!
      let mut xsVars := #[]
      for i in [:xs.size] do
        if atomData.argKinds[i]! != ArgKind.Constant then
          xsVars := xsVars.push xsVarsPre[i]!
      trace[Meta.debug] "xsVars: {(← xsVars.mapM (·.getDecl)).map (·.userName)}"

      trace[Meta.debug] "before PAT "
      trace[Meta.debug] "abo : {atomData.impConstrs}"
      trace[Meta.debug] "constrs: {constraints}"
      -- Add bconds declarations.
      let bconds := atomData.bconds.map fun (n,c) => (n, mkAppNBeta c xs)
      let pat ← withLocalDeclsDNondep bconds fun bs => do
        let bcondsDecls ← bs.mapM (·.fvarId!.getDecl)
        DCP.mkProcessedAtomTree objCurv objFun constraints.toList originalVarsDecls
          (extraVars := xsVars) (extraDecls := bcondsDecls)

      trace[Meta.debug] "after PAT "
      -- `pat` is the atom tree resulting from the DCP procedure.

      -- Temporary check until using atoms in graph implementations is supported.
      -- if pat.newVarDecls.length ≠ 0 ∨ pat.newConstrs.size ≠ 0 then
      --   throwError "Using nontrivial atoms in graph implementations is not yet supported"

      trace[Meta.debug] "pat.originalVarsDecls : {pat.originalVarsDecls.map (·.userName)}"
      trace[Meta.debug] "pat.newVarDecls : {pat.newVarDecls.map (·.userName)}"
      trace[Meta.debug] "pat.newConstrVarsArray : {pat.newConstrVarsArray.map (·.userName)}"

      withExistingLocalDecls originalVarsDecls.toList do
        withExistingLocalDecls pat.newVarDecls do
          withExistingLocalDecls pat.newConstrVarsArray.toList do
            trace[Meta.debug] "pat opt: {pat.optimality}"
            for c in pat.optimality.constrs.map Tree.val do
              trace[Meta.debug] "pat opt constr: {c}"
              check c
            -- `vs1` are the variables already present in the uncanon graph implementation.
            let vs1 := originalVarsDecls.map (mkFVar ·.fvarId)
            -- `vs2` are the variables to be added to the graph implementation.
            let vs2 := pat.newVarDecls.toArray.map (mkFVar ·.fvarId)
            let vs1Sol := atomData.solution.map fun s => mkAppNBeta s xs
            trace[Meta.debug] "vs1: {vs1}"
            trace[Meta.debug] "vs2: {vs2}"
            trace[Meta.debug] "vs1Sol: {vs1Sol}"
            trace[Meta.debug] "xs: {xs}"

            -- TODO: move because copied from DCP tactic.
            let canonConstrs := pat.canonExprs.constrs.map Tree.val
            let canonConstrs := canonConstrs.filterIdx (fun i => ¬ pat.isVCond[i]!)

            -- TODO: move because copied from DCP tactic.
            let newConstrProofs := pat.feasibility.fold #[] fun acc fs =>
              fs.fold acc Array.append

            -- for sc in solEqAtomProofs do
            --   trace[Meta.debug] "solEqAtomProofs: {← inferType sc}"

            for ncp in newConstrProofs do
              trace[Meta.debug] "newConstrProofs: {← inferType ncp}"

            -- let test := ← atomData.feasibility.mapM (fun e =>
            --   Meta.forallTelescope e (fun xs a => do
            --     trace[Meta.debug] "a: {←inferType a}"))

            let vconds := atomData.vconds.map fun (n,c) => (n, mkAppNBeta c xs)
            let bconds := atomData.bconds.map fun (n,c) => (n, mkAppNBeta c xs)

            let solEqAtomProofs := pat.solEqAtom.constrs.map Tree.val

            if atomData.feasibility.size != solEqAtomProofs.size then
              throwError ("Expected same length: {atomData.feasibility} and " ++
                "{solEqAtomProofs}")

            let solEqAtomProofs := pat.solEqAtom.constrs.map Tree.val
            let mut oldFeasibilityAdjusted := #[]

            for i in [:atomData.feasibility.size] do
              let feas := atomData.feasibility[i]!
              let feasXs := mkAppNBeta feas xs
              let adjustedFeas ←
                withLocalDeclsDNondep vconds fun cs => do
                  withLocalDeclsDNondep bconds fun bs => do
                    let feasXsVconds := mkAppNBeta feasXs cs
                    let feasXsConds := mkAppNBeta feasXsVconds bs
                    let proofAdjusted := solEqAtomProofs[i]!.replaceFVars vs1 vs1Sol
                    let adjustedFeas ← mkAppM ``Eq.mpr #[proofAdjusted, feasXsConds]
                    mkLambdaFVars (xs ++ cs ++ bs) adjustedFeas
              oldFeasibilityAdjusted := oldFeasibilityAdjusted.push adjustedFeas

            for proof in solEqAtomProofs do
              trace[Meta.debug] "solEqAtomProofs: {← inferType proof}"

            for feas in oldFeasibilityAdjusted do
              trace[Meta.debug] "oldFeasibilityAdjusted: {← inferType feas}"

            let newFeasibility ← newConstrProofs.mapM (fun e =>
              withLocalDeclsDNondep vconds fun cs => do
                withLocalDeclsDNondep bconds fun bs => do
                  mkLambdaFVars (xs ++ cs ++ bs) (e.replaceFVars vs1 vs1Sol))

            for f in atomData.feasibility do
              trace[Meta.debug] "feasibility: {← inferType f}"

            for nf in newFeasibility do
              trace[Meta.debug] "newFeasibility: {← inferType nf}"

            let constraintsFromCanonConstraints :=
              pat.optimality.constrs.map Tree.val

            for cfrc in constraintsFromCanonConstraints do
              trace[Meta.debug] "constraintsFromCanonConstraints: {← inferType cfrc}"

            if canonConstrs.size != constraintsFromCanonConstraints.size then
              throwError ("Expected same length: {canonConstrs} and " ++
                "{constraintsFromCanonConstraints}")

            let objFunFromCanonObjFun := pat.optimality.objFun.val
            trace[Meta.debug] "objFunFromCanonObjFun: {← inferType objFunFromCanonObjFun}"

            trace[Meta.debug] "pat.optimality.objFun: {← inferType atomData.optimality}"

            let newOptimality ←
              withLocalDeclsDNondep bconds fun bs => do
                let optimalityXsBConds := mkAppN atomData.optimality (xs ++ bs ++ vs1)
                trace[Meta.debug] "newOptimality: {← inferType optimalityXsBConds}"
                withLocalDeclsDNondep (canonConstrs.map (fun rc => (`_, rc))) fun cs => do
                  -- First, apply all constraints.
                  let mut optimalityAfterCanon := optimalityXsBConds
                  for i in [:canonConstrs.size] do
                    trace[Meta.debug] "optimalityAfterCanon: {← inferType optimalityAfterCanon}"
                    let c := mkApp constraintsFromCanonConstraints[i]! cs[i]!
                    optimalityAfterCanon := mkApp optimalityAfterCanon c
                  -- Then, adjust the condition using `objFunFromCanonObjFun`.
                  trace[Meta.debug] "optimalityAfterCanon: {← inferType optimalityAfterCanon}"
                  let monoArgsCount := getMonoArgsCount objCurv atomData.argKinds
                  let optimalityAfterApplyWithConditionAdjusted ←
                    lambdaTelescope (← whnf optimalityAfterCanon) <| fun xs e => do
                    -- Every extra argument has an extra condition, e.g. x', x ≤ x.
                    trace[Meta.debug] "xs: {xs}"
                    let monoArgs := xs[:2 * monoArgsCount]
                    trace[Meta.debug] "monoArgs: {monoArgs}"
                    trace[Meta.debug] "e: {← inferType e}"
                    let optCondition ← mkLambdaFVars xs[2 * monoArgsCount:] e
                    let newCond ←
                      if atomData.curvature == Curvature.Convex then
                        mkAppOptM ``le_trans #[
                          atomRange, none, none, none, none,
                          optCondition, objFunFromCanonObjFun]
                      else
                        -- TODO: concave. but convex_set too?
                        mkAppOptM ``le_trans #[
                          atomRange, none, none, none, none,
                          objFunFromCanonObjFun, optCondition]
                    mkLambdaFVars monoArgs newCond

                  trace[Meta.debug] "optimalityAfterApplyWithConditionAdjusted: {← inferType optimalityAfterApplyWithConditionAdjusted}"
                  trace[Meta.debug] "newOptimality applied: {← inferType optimalityAfterCanon}"
                  let ds := pat.newConstrVarsArray.map (mkFVar ·.fvarId)
                  mkLambdaFVars (xs ++ bs ++ vs1 ++ vs2 ++ cs ++ ds) optimalityAfterApplyWithConditionAdjusted

            trace[Meta.debug] "newOptimality: {← inferType newOptimality}"

            let mut newVCondElims := #[]
            for vcondElim in atomData.vcondElim do
              let newVCondElim := mkAppN vcondElim (xs ++ vs1)
              let newVCondElim ←
                withLocalDeclsDNondep (canonConstrs.map (fun rc => (`_, rc))) fun cs => do
                  let mut newVCondElim := newVCondElim
                  for i in [:canonConstrs.size] do
                    let c := mkApp constraintsFromCanonConstraints[i]! cs[i]!
                    newVCondElim := mkApp newVCondElim c
                  let ds := pat.newConstrVarsArray.map (mkFVar ·.fvarId)
                  mkLambdaFVars (xs ++ vs1 ++ vs2) <| ← mkLambdaFVars (cs ++ ds) newVCondElim
              newVCondElims := newVCondElims.push newVCondElim

            let atomData' : GraphAtomData := {  atomData with
              impVars := atomData.impVars.append
                (← pat.newVarDecls.toArray.mapM fun decl => do
                  return (decl.userName, ← mkLambdaFVars xs decl.type))
              impObjFun := ← mkLambdaFVars xs $ ← mkLambdaFVars (vs1 ++ vs2) $
                  pat.canonExprs.objFun.val
              impConstrs := ← (canonConstrs ++ pat.newConstrs).mapM
                (fun c => do
                  withLocalDeclsDNondep bconds fun bs => do
                    return ← mkLambdaFVars xs <| ← mkLambdaFVars bs <| ← mkLambdaFVars (vs1 ++ vs2) c)
              solution := atomData.solution.append
                (← pat.forwardImagesNewVars.mapM (fun e => mkLambdaFVars xs
                    (e.replaceFVars vs1 vs1Sol)))
              feasibility := oldFeasibilityAdjusted ++ newFeasibility
              optimality := newOptimality
              vcondElim := newVCondElims

              }

            return atomData'

end MultiLevel

end CvxLean
