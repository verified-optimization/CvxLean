import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Minimization
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Tactic.DCP.AtomSyntax
import CvxLean.Lib.Math.Data.Real
import CvxLean.Tactic.DCP.DCP

namespace CvxLean

open Lean Expr Meta Elab Command

/-- -/
def mkAndIntro (xs : Array Expr) : MetaM Expr := do
  let mut res := xs[xs.size-1]!
  for i in [:xs.size-1] do
    res ← mkAppM ``And.intro #[xs[xs.size-2-i]!, res]
  return res

/-- -/
def mkExistsFVars (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut res := e
  for i in [:xs.size] do
    let x := xs[xs.size-i-1]!
    res ← mkAppM ``Exists #[← mkLambdaFVars #[x] res]
  return res

/-- -/
def mkExistsIntro (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut res := e
  for i in [:xs.size] do
    let x := xs[xs.size-i-1]!
    res ← mkAppOptM ``Exists.intro #[none, some $ ← mkLambdaFVars #[x] (← inferType res), some x, some res]
  return res

/-- -/
def mkLetFVarsWith (e : Expr) (xs : Array Expr) (ts : Array Expr) : MetaM Expr := do
  if xs.size != ts.size then throwError "Expected same length: {xs} and {ts}"
  let mut e := e.abstract xs
  for i in [:xs.size] do
    let n := (← FVarId.getDecl xs[xs.size-1-i]!.fvarId!).userName
    e := mkLet n (← inferType xs[xs.size-1-i]!) ts[xs.size-1-i]! e
  return e

-- TODO: This does not respect namespaces.
/-- Introduce new names for the proofs in the atom to speed up proof building later. -/
def addAtomDataDecls (id : Lean.Name) (atomData : GraphAtomData) : CommandElabM GraphAtomData := do
  if atomData.solEqAtom.hasMVar then
    throwError "has mvar {atomData.solEqAtom}"
  let solEqAtom ← addAtomDataDecl (id.mkStr "solEqAtom") atomData.solEqAtom
  let optimality ← addAtomDataDecl (id.mkStr "optimality") atomData.optimality
  let mut feasibility := #[]
  for i in [:atomData.feasibility.size] do
    feasibility := feasibility.push $
      ← addAtomDataDecl (id.mkStr (s!"feasibility{i}")) atomData.feasibility[i]!
  let mut vcondElim := #[]
  for i in [:atomData.vcondElim.size] do
    vcondElim := vcondElim.push $
      ← addAtomDataDecl (id.mkStr (s!"vcondElim{i}")) atomData.vcondElim[i]!
  return {atomData with
    solEqAtom := solEqAtom
    feasibility := feasibility
    vcondElim := vcondElim
    optimality := optimality
  }
where
  addAtomDataDecl (name : Lean.Name) (expr : Expr) : CommandElabM Expr := do
    liftCoreM <| addDecl <| .defnDecl {
      name := name
      levelParams := []
      type := ← liftTermElabM (do return ← inferType expr)
      value := expr
      hints := .regular (getMaxHeight (← getEnv) expr + 1)
      safety := .safe
    }
    return mkConst name


/-- -/
def withCopyOfMonoXs {α} [Inhabited α] (xs : Array Expr) (argKinds : Array ArgKind) (f : Array Expr → Array Expr → Array ArgKind → TermElabM α) : TermElabM α := do
  -- Determine subset of monotone arguments and their behavior.
  let mut argDeclInfo : Array (Lean.Name × (Array Expr → TermElabM Expr)) := #[]
  let mut monoXs := #[]
  let mut monoArgKind := #[]
  for i in [:xs.size] do
    if argKinds[i]! != ArgKind.Constant ∧ argKinds[i]! != ArgKind.Neither then
      let ty := ← inferType xs[i]!
      let name := (← FVarId.getDecl xs[i]!.fvarId!).userName
      argDeclInfo := argDeclInfo.push (name, fun _ => pure ty)
      monoXs := monoXs.push xs[i]!
      monoArgKind := monoArgKind.push argKinds[i]!

  withLocalDeclsD argDeclInfo fun ys => do
    return ← f monoXs ys monoArgKind

/-- -/
def shiftingArgs (curv : Curvature) (xs : Array Expr) (argKinds : Array ArgKind) (mkConcl : Array Expr → Array Expr → TermElabM Expr) : TermElabM Expr :=
  withCopyOfMonoXs xs argKinds fun monoXs ys monoArgKind => do
    let mut ty := ← mkConcl monoXs ys
    for i' in [:monoXs.size] do
      let i := monoXs.size - 1 - i'
      ty ← match curvatureInArg curv monoArgKind[i]! with
      | Curvature.Concave => mkArrow (← mkLe monoXs[i]! ys[i]!) ty
      | Curvature.Convex => mkArrow (← mkLe ys[i]! monoXs[i]!) ty
      | _ => throwError "invalid curvature"
    return ← mkForallFVars ys ty

/-- TODO: just the number of relevant opt args. -/
def getMonoArgsCount (curv : Curvature) (argKinds : Array ArgKind) : ℕ :=
  argKinds.foldl (fun acc argKind =>
    match curvatureInArg curv argKind with
      | Curvature.Concave => 1 + acc
      | Curvature.Convex => 1 + acc
      | _ => acc) 0

/-- Use the DCP procedure to reduce the graph implementation to a problem that
uses only cone constraints and affine atoms. -/
def reduceAtomData (objCurv : Curvature) (atomData : GraphAtomData) : CommandElabM GraphAtomData := do
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
            for c in pat.optimality.constr.map Tree.val do
              trace[Meta.debug] "pat opt constr: {c}"
              check c
            -- `vs1` are the variables already present in the unreduced graph implementation.
            let vs1 := originalVarsDecls.map (mkFVar ·.fvarId)
            -- `vs2` are the variables to be added to the graph implementation.
            let vs2 := pat.newVarDecls.toArray.map (mkFVar ·.fvarId)
            let vs1Sol := atomData.solution.map fun s => mkAppNBeta s xs
            trace[Meta.debug] "vs1: {vs1}"
            trace[Meta.debug] "vs2: {vs2}"
            trace[Meta.debug] "vs1Sol: {vs1Sol}"
            trace[Meta.debug] "xs: {xs}"

            -- TODO: move because copied from DCP tactic.
            let reducedConstrs := pat.reducedExprs.constr.map Tree.val
            let reducedConstrs := reducedConstrs.filterIdx (fun i => ¬ pat.isVCond[i]!)

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

            let solEqAtomProofs := pat.solEqAtom.constr.map Tree.val

            if atomData.feasibility.size != solEqAtomProofs.size then
              throwError ("Expected same length: {atomData.feasibility} and " ++
                "{solEqAtomProofs}")

            let solEqAtomProofs := pat.solEqAtom.constr.map Tree.val
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

            let constraintsFromReducedConstraints :=
              pat.optimality.constr.map Tree.val

            for cfrc in constraintsFromReducedConstraints do
              trace[Meta.debug] "constraintsFromReducedConstraints: {← inferType cfrc}"

            if reducedConstrs.size != constraintsFromReducedConstraints.size then
              throwError ("Expected same length: {reducedConstrs} and " ++
                "{constraintsFromReducedConstraints}")

            let objFunFromReducedObjFun := pat.optimality.objFun.val
            trace[Meta.debug] "objFunFromReducedObjFun: {← inferType objFunFromReducedObjFun}"

            trace[Meta.debug] "pat.optimality.objFun: {← inferType atomData.optimality}"

            let newOptimality ←
              withLocalDeclsDNondep bconds fun bs => do
                let optimalityXsBConds := mkAppN atomData.optimality (xs ++ bs ++ vs1)
                trace[Meta.debug] "newOptimality: {← inferType optimalityXsBConds}"
                withLocalDeclsDNondep (reducedConstrs.map (fun rc => (`_, rc))) fun cs => do
                  -- First, apply all constraints.
                  let mut optimalityAfterReduced := optimalityXsBConds
                  for i in [:reducedConstrs.size] do
                    trace[Meta.debug] "optimalityAfterReduced: {← inferType optimalityAfterReduced}"
                    let c := mkApp constraintsFromReducedConstraints[i]! cs[i]!
                    optimalityAfterReduced := mkApp optimalityAfterReduced c
                  -- Then, adjust the condition using `objFunFromReducedObjFun`.
                  trace[Meta.debug] "optimalityAfterReduced: {← inferType optimalityAfterReduced}"
                  let monoArgsCount := getMonoArgsCount objCurv atomData.argKinds
                  let optimalityAfterApplyWithConditionAdjusted ←
                    lambdaTelescope (← whnf optimalityAfterReduced) <| fun xs e => do
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
                          optCondition, objFunFromReducedObjFun]
                      else
                        -- TODO: concave. but convex_set too?
                        mkAppOptM ``le_trans #[
                          atomRange, none, none, none, none,
                          objFunFromReducedObjFun, optCondition]
                    mkLambdaFVars monoArgs newCond

                  trace[Meta.debug] "optimalityAfterApplyWithConditionAdjusted: {← inferType optimalityAfterApplyWithConditionAdjusted}"
                  trace[Meta.debug] "newOptimality applied: {← inferType optimalityAfterReduced}"
                  let ds := pat.newConstrVarsArray.map (mkFVar ·.fvarId)
                  mkLambdaFVars (xs ++ bs ++ vs1 ++ vs2 ++ cs ++ ds) optimalityAfterApplyWithConditionAdjusted

            trace[Meta.debug] "newOptimality: {← inferType newOptimality}"

            let mut newVCondElims := #[]
            for vcondElim in atomData.vcondElim do
              let newVCondElim := mkAppN vcondElim (xs ++ vs1)
              let newVCondElim ←
                withLocalDeclsDNondep (reducedConstrs.map (fun rc => (`_, rc))) fun cs => do
                  let mut newVCondElim := newVCondElim
                  for i in [:reducedConstrs.size] do
                    let c := mkApp constraintsFromReducedConstraints[i]! cs[i]!
                    newVCondElim := mkApp newVCondElim c
                  let ds := pat.newConstrVarsArray.map (mkFVar ·.fvarId)
                  mkLambdaFVars (xs ++ vs1 ++ vs2) <| ← mkLambdaFVars (cs ++ ds) newVCondElim
              newVCondElims := newVCondElims.push newVCondElim

            let atomData' : GraphAtomData := {  atomData with
              impVars := atomData.impVars.append
                (← pat.newVarDecls.toArray.mapM fun decl => do
                  return (decl.userName, ← mkLambdaFVars xs decl.type))
              impObjFun := ← mkLambdaFVars xs $ ← mkLambdaFVars (vs1 ++ vs2) $
                  pat.reducedExprs.objFun.val
              impConstrs := ← (reducedConstrs ++ pat.newConstrs).mapM
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

              -- TODO: solEqAtom := sorry. ?????????

            return atomData'

/-- -/
def elabCurvature (curv : Syntax) : TermElabM Curvature := do
  match curv.getId with
  | `«convex» => return Curvature.Convex
  | `«concave» => return Curvature.Concave
  | `«affine» => return Curvature.Affine
  | `«convex_set» => return Curvature.ConvexSet
  | _ => throwError "Unknown curvature : {curv.getId}"

/-- -/
def elabExpr (expr : Syntax) (argDecls : Array LocalDecl) (ty : Option Expr := none): TermElabM (Expr × Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let body ← Elab.Term.elabTermAndSynthesizeEnsuringType expr ty
    let bodyTy ← inferType body
    return (← mkLambdaFVars xs body, bodyTy)

/-- -/
def elabArgKindsAux : List Syntax → TermElabM (List LocalDecl × List ArgKind)
| [] => pure ([], [])
| List.cons stx stxs => do
  match stx with
  | `(arg_with_kind|($id : $ty) $argkind) => do
    let ty ← Term.elabTerm ty.raw none
    withLocalDeclD id.getId ty fun x => do
      let argkind ←
        match argkind.raw with
        | `(arg_kind| +) => pure $ ArgKind.Increasing
        | `(arg_kind| -) => pure $ ArgKind.Decreasing
        | `(arg_kind| ?) => pure $ ArgKind.Neither
        | `(arg_kind| &) => pure $ ArgKind.Constant
        | _ => throwError "Unknown argument kind {argkind}"
      let argDecl ← x.fvarId!.getDecl
      let (argDecls, argKinds) ← elabArgKindsAux stxs
      return (argDecl :: argDecls, argkind :: argKinds)
  | _ => throwUnsupportedSyntax

/-- -/
def elabArgKinds (args : Array Syntax) : TermElabM (Array LocalDecl × Array ArgKind) := do
  let (argDecls, argKinds) ← elabArgKindsAux args.toList
  return (argDecls.toArray, argKinds.toArray)

/-- -/
def elabVConditions (argDecls : Array LocalDecl) (vcondStx : Array Syntax) :
  TermElabM (Array (Lean.Name × Expr) × Std.HashMap Lean.Name Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let mut vcondMap : Std.HashMap Lean.Name Expr := {}
    let mut vconds : Array (Lean.Name × Expr) := #[]
    for stx in vcondStx do
      let vcond ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] (some $ mkSort levelZero)
      let vcond ← mkLambdaFVars xs vcond
      vcondMap := vcondMap.insert stx[1].getId vcond
      vconds := vconds.push (stx[1].getId, vcond)
    return (vconds, vcondMap)

/-- Assumtions can be elaborated exactly like vconditions. -/
def elabBConds := elabVConditions

/-- -/
def elabImpVars (argDecls : Array LocalDecl) (impVarsStx : Array Syntax) :
  TermElabM (Array (Lean.Name × Expr) × Std.HashMap Lean.Name Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let mut impVarMap : Std.HashMap Lean.Name Expr := {}
    let mut impVars : Array (Lean.Name × Expr) := #[]
    for stx in impVarsStx do
      let impVarTy ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] none
      let impVarTy ← mkLambdaFVars xs $ impVarTy
      impVars := impVars.push (stx[1].getId, impVarTy)
      impVarMap := impVarMap.insert stx[1].getId impVarTy
    return (impVars, impVarMap)

/-- -/
def elabImpObj (argDecls : Array LocalDecl) (impVars : Array (Lean.Name × Expr))
    (impObjStx : Syntax) (bodyTy : Expr) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun ts => do
      let impObj ← Elab.Term.elabTermAndSynthesizeEnsuringType impObjStx (some bodyTy)
      return ← mkLambdaFVars xs $ ← mkLambdaFVars ts impObj

/-- -/
def elabImpConstrs (argDecls : Array LocalDecl) (impVars : Array (Lean.Name × Expr))
    (bconds : Array (Lean.Name × Expr)) (impConstrStx : Array Syntax) :
    TermElabM (Array (Lean.Name × Expr)) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
    withLocalDeclsDNondep bconds fun as => do
      withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
        let mut impConstrs : Array (Lean.Name × Expr) := #[]
        for stx in impConstrStx do
          let impConstr ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] (mkSort levelZero)
          let impConstr ← mkLambdaFVars xs <| ← mkLambdaFVars as <| ← mkLambdaFVars vs impConstr
          trace[Meta.debug] "impConstr: {← inferType impConstr}"
          impConstrs := impConstrs.push (stx[1].getId, impConstr)
        return impConstrs

/-- -/
def elabSols (argDecls : Array LocalDecl) (impVars : Array (Lean.Name × Expr))
    (impVarMap : Std.HashMap Lean.Name Expr) (solStx : Array Syntax) : TermElabM (Array Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let impVarNames := impVars.map (·.fst)
    let mut solMap : Std.HashMap Lean.Name Expr := {}
    for stx in solStx do
      let id ← match impVarMap.find? stx[1].getId with
      | some id => pure id
      | none => throwError "Unknown variable: {stx[1].getId}"
      let ty := mkAppNBeta id xs
      solMap := solMap.insert stx[1].getId $ ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] (some ty)
    let sols ← impVarNames.mapM
      fun n => match solMap.find? n with
        | some sol => pure sol
        | none => throwError "solution not found {n}"
    let sols ← sols.mapM (do return ← mkLambdaFVars xs ·)
    return sols

/-- -/
def elabSolEqAtom (argDecls : Array LocalDecl) (vconds : Array (Lean.Name × Expr))
    (impObj : Expr) (sols : Array Expr)
    (expr : Expr) (stx : Syntax) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let vconds := vconds.map fun (n,c) => (n, mkAppNBeta c xs)
    withLocalDeclsDNondep vconds fun cs => do
      let body := mkAppNBeta expr xs
      let impObj := mkAppNBeta impObj xs
      let sols := sols.map (mkAppNBeta · xs)
      let impObj' := convertLambdasToLets impObj sols
      let ty ← mkEq impObj' body
      trace[Meta.debug] "ensuring type {ty}"
      let solEqAtom ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
      return ← mkLambdaFVars xs $ ← mkLambdaFVars cs solEqAtom

/-- -/
def elabFeas (argDecls : Array LocalDecl) (vconds bconds : Array (Lean.Name × Expr))
    (impConstrs : Array (Lean.Name × Expr)) (sols : Array Expr) (stx : Array Syntax) : TermElabM (Array Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let bconds := bconds.map fun (n, c) => (n, mkAppNBeta c xs)
    withLocalDeclsDNondep bconds fun as => do
      let vconds := vconds.map fun (n, c) => (n, mkAppNBeta c xs)
      withLocalDeclsDNondep vconds fun cs => do
      let impConstrs := impConstrs.map fun (n, c) => (n, mkAppNBeta c xs)
      let impConstrs := impConstrs.map fun (n, c) => (n, mkAppNBeta c as)
      let sols := sols.map (mkAppNBeta · xs)
      let mut feas := #[]
      for i in [:impConstrs.size] do
        if (stx[i]!)[1]!.getId != impConstrs[i]!.1 then
          throwError "Feasibility: Expected {impConstrs[i]!.1}, found {(stx[i]!)[1]!}"
        let ty := convertLambdasToLets impConstrs[i]!.2 sols
        let f ← Elab.Term.elabTermAndSynthesizeEnsuringType (stx[i]!)[3]! (some ty)
        let f ← mkLambdaFVars xs $ ← mkLambdaFVars as $ ← mkLambdaFVars cs f
        feas := feas.push f
      return feas

/-- -/
def withCopyOfNonConstVars (xs : Array Expr) (argKinds : Array ArgKind) (f : Array Expr → Array Expr → TermElabM Expr) :
  TermElabM Expr := do
  -- Determine subset of non-constant arguments.
  let mut argDeclInfo : Array (Lean.Name × (Array Expr → TermElabM Expr)) := #[]
  for i in [:xs.size] do
    if argKinds[i]! != ArgKind.Constant then
      let ty := ← inferType xs[i]!
      let name := Name.mkSimple ((ToString.toString (← FVarId.getDecl xs[i]!.fvarId!).userName) ++ "'")
      argDeclInfo := argDeclInfo.push (name, fun _ => pure ty)

  withLocalDeclsD argDeclInfo fun ys => do
    let mut allYs := #[]
    let mut j := 0
    for i in [:xs.size] do
      -- use old variable if constant, otherwise use new variable
      if argKinds[i]! == ArgKind.Constant then
        allYs := allYs.push xs[i]!
      else
        allYs := allYs.push ys[j]!
        j := j + 1
    return ← f ys allYs



/-- -/
def elabOpt (curv : Curvature) (argDecls : Array LocalDecl) (expr : Expr) (bconds : Array (Lean.Name × Expr))
    (impVars : Array (Lean.Name × Expr)) (impObj : Expr) (impConstrs : Array (Lean.Name × Expr))
    (argKinds : Array ArgKind) (stx : Syntax) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
    withLocalDeclsDNondep bconds fun as => do
      withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c xs)
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c as)
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c vs)
        withLocalDeclsDNondep impConstrs fun is => do
          let impObj := mkAppNBeta (mkAppNBeta impObj xs) vs
          let ty ← shiftingArgs curv xs argKinds fun monoXs ys =>
            let body := mkAppNBeta expr xs
            let body := body.replaceFVars monoXs ys
            match curv with
            | Curvature.Concave => return ← mkLe impObj body
            | Curvature.Convex => return ← mkLe body impObj
            | _ => throwError "invalid curvature: {curv}"
          trace[Meta.debug] "elabOpt ensuring {ty}"
          let opt ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
          trace[Meta.debug] "elabOpt opt: {← inferType opt}"
          return ← mkLambdaFVars xs $ ← mkLambdaFVars as $ ← mkLambdaFVars vs $ ← mkLambdaFVars is opt

/-- -/
def elabVCondElim (curv : Curvature) (argDecls : Array LocalDecl) (bconds vconds : Array (Lean.Name × Expr)) (vcondMap : Std.HashMap Lean.Name Expr)
    (impVars : Array (Lean.Name × Expr)) (impConstrs : Array (Lean.Name × Expr)) (argKinds : Array ArgKind) (stx : Array Syntax) : TermElabM (Array Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c xs)
    let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
    withLocalDeclsDNondep bconds fun as => do
      let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c as)
      withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c vs)
        withLocalDeclsDNondep impConstrs fun is => do
          let mut vcondElimMap : Std.HashMap Lean.Name Expr := {}
          for i in [:stx.size] do
            let ty ← shiftingArgs curv xs argKinds fun monoXs ys => do
              let id ← match vcondMap.find? (stx[i]!)[1]!.getId with
              | some id => pure id
              | none => throwError "Unknown vcondition: {(stx[i]!)[1]!.getId}"
              let body := mkAppNBeta id xs
              let body := body.replaceFVars monoXs ys
              return body
            let vcondElim ← Elab.Term.elabTermAndSynthesizeEnsuringType (stx[i]!)[3]! (some $ ty)
            let vcondElim ← mkLambdaFVars xs $ ← mkLambdaFVars vs $ ← mkLambdaFVars is vcondElim
            vcondElimMap := vcondElimMap.insert (stx[i]!)[1]!.getId vcondElim
          return ← vconds.mapM
            fun (n, _) => match vcondElimMap.find? n with
              | some vcond => pure vcond
              | none => throwError "vcondition not found: {n}"

/-- -/
@[command_elab atomCommand] unsafe def elabAtomCommand : CommandElab
| `(declare_atom $id [ $curv ] $args* : $expr :=
    vconditions $vconds*
    implementationVars $impVars*
    implementationObjective $impObj
    implementationConstraints $impConstrs*
    solution $sols*
    solutionEqualsAtom $solEqAtom
    feasibility $feas*
    optimality $opt
    vconditionElimination $vcondElim*) => do
  let atomData ← liftTermElabM do
    -- TODO: check if trating convexset as convex makes sense.
    let curvTag ← elabCurvature curv.raw
    let curv := if curvTag == Curvature.ConvexSet then Curvature.Concave else curvTag
    let (argDecls, argKinds) ← elabArgKinds args.rawImpl
    let (expr, bodyTy) ← elabExpr expr.raw argDecls
    let (vconds, vcondMap) ← elabVConditions argDecls vconds.rawImpl
    let (impVars, impVarMap) ← elabImpVars argDecls impVars.rawImpl
    let impObj ← elabImpObj argDecls impVars impObj.raw bodyTy
    let impConstrs ← elabImpConstrs argDecls impVars #[] impConstrs.rawImpl
    let sols ← elabSols argDecls impVars impVarMap sols.rawImpl
    let solEqAtom ← elabSolEqAtom argDecls vconds impObj sols expr solEqAtom.raw
    let feas ← elabFeas argDecls vconds #[] impConstrs sols feas.rawImpl
    let opt ← elabOpt curv argDecls expr #[] impVars impObj impConstrs argKinds opt.raw
    let vcondElim ← elabVCondElim curv argDecls #[] vconds vcondMap impVars impConstrs argKinds vcondElim.rawImpl

    let atomData := {
      id := id.getId
      curvature := curvTag
      expr := expr
      argKinds := argKinds
      bconds := #[]
      vconds := vconds
      impVars := impVars
      impObjFun := impObj
      impConstrs := impConstrs.map (·.snd)
      solution := sols
      solEqAtom := solEqAtom
      feasibility := feas
      optimality := opt
      vcondElim := vcondElim
    }
    return atomData

  let objCurv := atomData.curvature
    -- match atomData.curvature with
    -- | Curvature.ConvexSet => Curvature.ConvexSet
    -- | _ => Curvature.Affine

  trace[Meta.debug] "before reduce sol eq atom: {atomData.solEqAtom}"

  let atomData ← reduceAtomData objCurv atomData
  -- trace[Meta.debug] "HERE Reduced atom: {atomData}"
  let atomData ← addAtomDataDecls id.getId atomData
  -- trace[Meta.debug] "HERE Added atom"

  liftTermElabM do
    trace[Meta.debug] "Add atom: {atomData}"
    addAtom $ AtomData.graph atomData
| _ => throwUnsupportedSyntax


/-- -/
@[command_elab atomWithBCondsCommand] unsafe def elabAtomWithBCondsCommand : CommandElab
| `(declare_atom $id [ $curv ] $args* : $expr :=
    bconditions $bconds*
    vconditions $vconds*
    implementationVars $impVars*
    implementationObjective $impObj
    implementationConstraints $impConstrs*
    solution $sols*
    solutionEqualsAtom $solEqAtom
    feasibility $feas*
    optimality $opt
    vconditionElimination $vcondElim*) => do
  let atomData ← liftTermElabM do
    let curv ← elabCurvature curv.raw
    let (argDecls, argKinds) ← elabArgKinds args.rawImpl
    let (expr, bodyTy) ← elabExpr expr.raw argDecls
    let (bconds, _) ← elabBConds argDecls bconds.rawImpl
    let (vconds, vcondMap) ← elabVConditions argDecls vconds.rawImpl
    let (impVars, impVarMap) ← elabImpVars argDecls impVars.rawImpl
    let impObj ← elabImpObj argDecls impVars impObj.raw bodyTy
    let impConstrs ← elabImpConstrs argDecls impVars bconds impConstrs.rawImpl
    let sols ← elabSols argDecls impVars impVarMap sols.rawImpl
    let solEqAtom ← elabSolEqAtom argDecls vconds impObj sols expr solEqAtom.raw
    let feas ← elabFeas argDecls vconds bconds impConstrs sols feas.rawImpl
    let opt ← elabOpt curv argDecls expr bconds impVars impObj impConstrs argKinds opt.raw
    let vcondElim ← elabVCondElim curv argDecls bconds vconds vcondMap impVars impConstrs argKinds vcondElim.rawImpl

    let atomData := {
      id := id.getId
      curvature := curv
      expr := expr
      argKinds := argKinds
      bconds := bconds
      vconds := vconds
      impVars := impVars
      impObjFun := impObj
      impConstrs := impConstrs.map (·.snd)
      solution := sols
      solEqAtom := solEqAtom
      feasibility := feas
      optimality := opt
      vcondElim := vcondElim
    }
    return atomData

  let atomData ← reduceAtomData atomData.curvature atomData--Curvature.Affine atomData
  let atomData ← addAtomDataDecls id.getId atomData

  liftTermElabM do
    trace[Meta.debug] "Add atom: {atomData}"
    addAtom $ AtomData.graph atomData
| _ => throwUnsupportedSyntax

/-- -/
def mapNonConstant (xs : Array Expr) (argKinds : Array ArgKind) (f : Expr → TermElabM Expr) :
  TermElabM (Array Expr) :=
    (Array.zip xs argKinds).mapM fun (x, kind) => do
      if kind == ArgKind.Constant
      then return x
      else return ← f x

/-- -/
def elabHom (argDecls : Array LocalDecl) (expr : Expr) (argKinds : Array ArgKind) (stx : Syntax) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    withLocalDeclD `κ (mkConst ``Real) fun κ => do
      let xs := argDecls.map (mkFVar ·.fvarId)
      let zero := mkAppNBeta expr $ ← mapNonConstant xs argKinds
        fun x => do return ← mkNumeral (← inferType x) 0
      let lhs ← mkAdd
        (← mkAppM ``HSMul.hSMul #[κ, mkAppNBeta expr xs])
        zero
      let rhs ← mkAdd
        (mkAppNBeta expr $ ← mapNonConstant xs argKinds
          fun x => mkAppM ``HSMul.hSMul #[κ, x])
        (← mkAppM ``HSMul.hSMul #[κ, zero])
      let ty ← mkEq lhs rhs
      let hom ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
      return ← mkLambdaFVars xs $ ← mkLambdaFVars #[κ] hom

def elabAdd (argDecls : Array LocalDecl) (expr : Expr) (argKinds : Array ArgKind) (stx : Syntax) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    withCopyOfNonConstVars xs argKinds fun newYs ys => do
      let zero := mkAppNBeta expr $ ← mapNonConstant xs argKinds
        fun x => do return ← mkNumeral (← inferType x) 0
      let lhs ← mkAdd (mkAppNBeta expr xs) (mkAppNBeta expr ys)
      let rhs ← mkAdd
        (mkAppNBeta expr $
          ← (Array.zip argKinds (Array.zip xs ys)).mapM fun (kind, x, y) => do
            if kind == ArgKind.Constant
            then return x
            else mkAdd x y)
        (zero)
      let ty ← mkEq lhs rhs
      let add ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
      return ← mkLambdaFVars xs $ ← mkLambdaFVars newYs add

/-- -/
@[command_elab affineAtomCommand] unsafe def elabAffineAtomCommand : CommandElab
| `(declare_atom $id [ affine ] $args* : $expr :=
    bconditions $bconds*
    homogenity $hom
    additivity $add
    optimality $opt) => do
  let atomData ← liftTermElabM do
    let (argDecls, argKinds) ← elabArgKinds args.rawImpl
    let (expr, bodyTy) ← elabExpr expr.raw argDecls
    let vconds := #[]
    let impVars := #[]
    let impObj := expr
    let impConstrs := #[]
    let sols := #[]
    let solEqAtom ← lambdaTelescope expr fun xs body => do return ← mkLambdaFVars xs $ ← mkEqRefl body
    let feas := #[]
    let (bconds, _) ← elabBConds argDecls bconds.rawImpl
    let hom ← elabHom argDecls expr argKinds hom.raw
    check hom -- Property is not saved. This is just a sanity check.
    let add ← elabAdd argDecls expr argKinds add.raw
    check add -- Property is not saved. This is just a sanity check.
    let optConcave ← elabOpt Curvature.Concave argDecls expr bconds impVars impObj impConstrs argKinds opt.raw
    let optConvex ←
      withExistingLocalDecls argDecls.toList do
        let xs := argDecls.map (mkFVar ·.fvarId)
        let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
        withLocalDeclsDNondep bconds fun as => do
          withCopyOfMonoXs xs argKinds fun monoXs ys monoArgKind => do
            let mut optInverted := optConcave
            let mut i' := 0
            for i in [:xs.size] do
              if argKinds[i]! != ArgKind.Constant ∧ argKinds[i]! != ArgKind.Neither then
                optInverted := mkApp optInverted ys[i']!
                i' := i' + 1
              else
                optInverted := mkApp optInverted xs[i]!
            optInverted := mkAppN optInverted as
            for i in [:xs.size] do
              if argKinds[i]! != ArgKind.Constant ∧ argKinds[i]! != ArgKind.Neither then
                optInverted := mkApp optInverted xs[i]!
            return ← mkLambdaFVars xs $ ← mkLambdaFVars as $ ← mkLambdaFVars ys optInverted
    let opt ← mkAppM ``And.intro #[optConcave, optConvex]
    let vcondElim := #[]

    let atomData := {
      id := id.getId
      curvature := Curvature.Affine
      expr := expr
      argKinds := argKinds
      vconds := vconds
      bconds := bconds
      impVars := impVars
      impObjFun := impObj
      impConstrs := impConstrs.map (·.snd)
      solution := sols
      solEqAtom := solEqAtom
      feasibility := feas
      optimality := opt
      vcondElim := vcondElim
    }
    return atomData

  let atomData ← addAtomDataDecls id.getId atomData

  liftTermElabM do
    trace[Meta.debug] "Add atom: {atomData}"
    addAtom $ AtomData.graph atomData
| _ => throwUnsupportedSyntax

/-- -/
@[command_elab coneAtomCommand] unsafe def elabConeAtomCommand : CommandElab
| `(declare_atom $id [ cone ] $args* : $expr :=
      optimality $opt) => do
  let atomData ← liftTermElabM do
    let (argDecls, argKinds) ← elabArgKinds args.rawImpl
    let (expr, bodyTy) ← elabExpr expr.raw argDecls (ty := some (mkSort levelZero))
    let vconds := #[]
    let impVars := #[]
    let impObj := expr
    let impConstrs := #[]
    let sols := #[]
    let solEqAtom ← lambdaTelescope expr fun xs body =>
      do return ← mkLambdaFVars xs $ ← mkEqRefl body
    let feas := #[]
    let bconds := #[]
    -- TODO: Not concave....
    let opt ← elabOpt Curvature.Concave argDecls expr bconds impVars impObj impConstrs argKinds opt.raw
    let vcondElim := #[]

    let atomData := {
      id := id.getId
      curvature := Curvature.ConvexSet --Curvature.Concave
      expr := expr
      argKinds := argKinds
      vconds := vconds
      bconds := bconds
      impVars := impVars
      impObjFun := impObj
      impConstrs := impConstrs.map (·.snd)
      solution := sols
      solEqAtom := solEqAtom
      feasibility := feas
      optimality := opt
      vcondElim := vcondElim
    }
    return atomData

  let atomData ← addAtomDataDecls id.getId atomData

  liftTermElabM do
    trace[Meta.debug] "Add atom: {atomData}"
    addAtom $ AtomData.graph atomData
| _ => throwUnsupportedSyntax

end CvxLean
