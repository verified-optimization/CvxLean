import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Missing.Meta
import CvxLean.Lib.Missing.Array
import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.DCP.OC
import CvxLean.Meta.Missing.Expr
import CvxLean.Tactic.Solver.Float.OptimizationParam

namespace CvxLean

open Lean Lean.Meta

namespace DCP

/-- Check if `expr` is constant by checking if it contains any free 
variable from `vars`. -/
def isConstant (expr : Expr) (vars : Array FVarId) : Bool := Id.run do
  let fvarSet := (collectFVars {} expr).fvarSet
  for v in vars do
    if fvarSet.contains v then return false
  return true

/-- Return list of all registered atoms that match with a given expression. 
For every registered atom, it returns: 
1. The list of arguments as Lean expressions for further matching. 
2. The atom entry, of type `GraphAtomData`. -/
def findRegisteredAtoms (e : Expr) : 
  MetaM (Array (Array Expr × GraphAtomData)) := do
  let discrTree ← getAtomDiscrTree
  let atoms ← discrTree.getMatch (← zetaReduce (← e.removeMData))
  trace[Meta.debug] "discrTree {atoms.size} {e}"
  let mut goodAtoms := #[]
  for atom in atoms do
    let (mvars, _, pattern) ← lambdaMetaTelescope atom.expr
    if ← isDefEq pattern e then
      let args ← mvars.mapM instantiateMVars
      goodAtoms := goodAtoms.push (args, atom.graph!)
    else
      trace[Meta.debug] "Pattern did not match. (Pattern {toString pattern}; Expression {toString e})"
  -- Heuristic sorting of potential atoms to use: larger expressions have priority:
  goodAtoms := goodAtoms.insertionSort (fun a b => (a.2.expr.size - b.2.expr.size != 0))
  return goodAtoms

/-- -/
inductive FindAtomResult
| Success (res : Tree GraphAtomData Expr × Tree (Array Expr) Unit × Tree Curvature Curvature × Tree (Array Expr) (Array Expr))
| Error (msgs : Array MessageData)

/-- -/
partial def findAtoms (e : Expr) (vars : Array FVarId) (curvature : Curvature) : MetaM (Bool × Array MessageData × Tree GraphAtomData Expr × Tree (Array Expr) Unit × Tree Curvature Curvature × Tree (Array Expr) (Array Expr)) := do
  if isConstant e vars then
    return (false, #[], Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
  if e.isFVar ∧ vars.contains e.fvarId! then
    return (false, #[], Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
  let potentialAtoms ← findRegisteredAtoms e
  let mut failedAtoms : Array MessageData := #[]
  if potentialAtoms.size == 0 then
    failedAtoms := failedAtoms.push m!"No atom found for {e}"
  for (args, atom) in potentialAtoms do
    match ← processAtom e vars curvature atom args with
    | FindAtomResult.Success (atoms, args, curvatures, bconds) =>
      return (false, failedAtoms, atoms, args, curvatures, bconds)
    | FindAtomResult.Error msg =>
      failedAtoms := failedAtoms ++ msg
  return (true, failedAtoms, Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
where
  processAtom (e : Expr) (vars : Array FVarId) (curvature : Curvature) (atom : GraphAtomData) (args : Array Expr) : MetaM FindAtomResult := do
    if atom.curvature != Curvature.Affine ∧ curvature != atom.curvature then
      return FindAtomResult.Error
        #[m!"Trying atom {atom.expr} for expression {e}: " ++ 
          m!"Expected {curvature}, but atom is {atom.curvature}"]
    let mut abort := false -- TODO: use exception instead?
    let mut bconds := #[]
    for (bcondName, bcondType) in atom.bconds do
      let bcondType := mkAppNBeta bcondType args
      trace[Meta.debug] "decls: {((← getLCtx).decls.map fun decl => decl.map fun decl => decl.type).toArray}"
      let fvarId? ← (← getLCtx).decls.findSomeM? fun decl => match decl with
        | none => pure none
        | some decl => do
          if ← isDefEq decl.type bcondType then return some decl.fvarId else return none
      match fvarId? with
      | some fvarId => 
        bconds := bconds.push (mkFVar fvarId)
      | none =>
        -- TODO: This is a hack. Trick to prove simple bconditions.
        let (e, _) ← Lean.Elab.Term.TermElabM.run $ Lean.Elab.Term.commitIfNoErrors? $ do
          let v ← Lean.Elab.Term.elabTerm (← `(by norm_num)).raw (some bcondType)
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let v ← instantiateMVars v
          return v
        if let some e' := e then 
          bconds := bconds.push e' 
        else 
          return FindAtomResult.Error
            #[m!"Trying atom {atom.expr} for expression {e}: " ++ 
              m!"Background Condition {bcondType} not found."]

    let mut childTrees := #[]
    let mut childArgsTrees := #[]
    let mut childCurvatures := #[]
    let mut childBConds := #[]
    for i in [:args.size] do
      let arg := args[i]!
      if atom.argKinds[i]! == ArgKind.Constant ∧ not (isConstant arg vars) then
        return FindAtomResult.Error
          #[m!"Trying atom {atom.expr} for expression {e}: " ++ 
            m!"Expected constant argument, but found: {arg}"]
      let c := curvatureInArg curvature atom.argKinds[i]!
      let (childFailed, childFailedAtoms, childTree, childArgsTree, childCurvature, childBCond) ← findAtoms arg vars c
      if childFailed then
        return FindAtomResult.Error childFailedAtoms
      childTrees := childTrees.push childTree
      childArgsTrees := childArgsTrees.push childArgsTree
      childCurvatures := childCurvatures.push childCurvature
      childBConds := childBConds.push childBCond
    if curvature == Curvature.Affine then
      -- For affine branches, we only check that all atoms are affine, but don't store the results.
      return FindAtomResult.Success (Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf bconds)
    else 
      return FindAtomResult.Success (Tree.node atom childTrees, Tree.node args childArgsTrees, Tree.node curvature childCurvatures, Tree.node bconds childBConds)

/-- -/
partial def mkNewVars (i : Nat) : Tree GraphAtomData Expr → Tree (Array Expr) Unit → MetaM (Tree (Array LocalDecl) Unit × Nat)
| Tree.node atom childAtoms, Tree.node args childArgs => do
  let mut childNewVars := #[]
  let mut i := i
  for k in [:childAtoms.size] do
    let (childNewVar, i') ← mkNewVars i childAtoms[k]! childArgs[k]!
    i := i'
    childNewVars := childNewVars.push $ childNewVar
  let mut newVars : Array LocalDecl := #[]
  for (n, ty) in atom.impVars do
    trace[Meta.debug] "new var type: {ty}"
    newVars := newVars.push $
      LocalDecl.cdecl 0 (← mkFreshFVarId) (Name.mkNum n i) (mkAppNBeta ty args) Lean.BinderInfo.default LocalDeclKind.default
    i := i + 1
  return (Tree.node newVars childNewVars, i)
| Tree.leaf _, Tree.leaf _ => pure (Tree.leaf (), i)
| _, _ => throwError "Tree mismatch"

/-- -/
def mkNewVarDeclList (newVars : OC (Tree (Array LocalDecl) Unit)) : 
  MetaM (List LocalDecl) := do
  let newVarTrees := #[newVars.objFun] ++ newVars.constr
  let mut newVarDecls := #[]
  for t in newVarTrees do
    newVarDecls := t.fold newVarDecls Array.append
  return newVarDecls.toList

/-- -/
partial def mkReducedExprs : Tree GraphAtomData Expr → Tree (Array LocalDecl) Unit → MetaM (Tree Expr Expr)
  | Tree.node atom childAtoms, Tree.node newVars childNewVars => do
    let mut childReducedExprs := #[]
    for i in [:childAtoms.size] do
      childReducedExprs := childReducedExprs.push $ ← mkReducedExprs childAtoms[i]! childNewVars[i]!
    let reducedExpr := atom.impObjFun
    let reducedExpr := mkAppNBeta reducedExpr (childReducedExprs.map (·.val))
    let reducedExpr := mkAppNBeta reducedExpr (newVars.map (mkFVar ·.fvarId))
    return Tree.node reducedExpr childReducedExprs
  | Tree.leaf e, Tree.leaf () => pure $ Tree.leaf e
  | _, _ => throwError "Tree mismatch"

/-- -/
partial def mkNewConstrs : Tree GraphAtomData Expr → Tree (Array LocalDecl) Unit → Tree Expr Expr → MetaM (Tree (Array Expr) Unit)
  | Tree.node atom childAtoms, Tree.node newVars childNewVars, Tree.node reducedExprs childReducedExprs => do
    let mut childNewConstrs := #[]
    for i in [:childAtoms.size] do
      childNewConstrs := childNewConstrs.push <| ← mkNewConstrs childAtoms[i]! childNewVars[i]! childReducedExprs[i]!
    let newConstrs := atom.impConstrs
    let newConstrs := newConstrs.map (mkAppNBeta · (childReducedExprs.map Tree.val))
    let newConstrs := newConstrs.map (mkAppNBeta · (newVars.map (mkFVar ·.fvarId)))
    return Tree.node newConstrs childNewConstrs
  | Tree.leaf _, Tree.leaf _, Tree.leaf _ => pure $ Tree.leaf ()
  | _, _, _ => throwError "Tree mismatch"

#check collectFVars

/-- -/
-- NOTE(RFM): Also return new constraints inferred.
partial def findVConditions (originalConstrVars : Array LocalDecl) (constraints : Array Expr) 
  (newConstraints : Array Expr) (newConstraintsDecl : Array LocalDecl) : 
  Tree GraphAtomData Expr → 
  Tree (Array Expr) Unit → 
  MetaM (Array Expr × Array LocalDecl × Tree (Array ℕ) Unit)
  | Tree.node atom childAtoms, Tree.node args childArgs => do
    let mut childVCondIdxs := #[]
    let mut newConstraintsDecl := newConstraintsDecl
    let mut newConstraints := newConstraints
    for i in [:childAtoms.size] do
      let (childNewConstrs, childNewConstrsDecl, childVCondIdx) ← 
        findVConditions originalConstrVars constraints #[] #[] childAtoms[i]! childArgs[i]!
      childVCondIdxs := childVCondIdxs.push childVCondIdx
      newConstraintsDecl := newConstraintsDecl ++ childNewConstrsDecl
      newConstraints := newConstraints ++ childNewConstrs
    
    -- let constraints := constraints ++ newConstraints
    let mut vcondIdx := #[]
    for (n, vcond) in atom.vconds do
      let vcond := mkAppNBeta vcond args
      
      -- First, try to see if it matches exactly with any of the constraints.
      match ← constraints.findIdxM? (isDefEq vcond) with
      | some i => do vcondIdx := vcondIdx.push i
      | none => 
        -- TODO(RFM): Same issue with background conditions. Find a less hacky way?
        -- Infer vconditions from constraints.
        let vcondProofTyBody ← liftM <| constraints.foldrM mkArrow vcond 
        let vcondProofTy ← mkForallFVars args vcondProofTyBody
        
        let (e, _) ← Lean.Elab.Term.TermElabM.run <| Lean.Elab.Term.commitIfNoErrors? <| do
            let tac ← `(by intros; try { norm_num } <;> try { positivity })
            let v ← Lean.Elab.Term.elabTerm tac.raw (some vcondProofTy)
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars v

        if let some e' := e then 
          -- The inferred variable condition is added to the context, and it will then 
          -- be removed in the condition elimination phase.
          let newCondition := mkAppNBeta e' args
          let newCondition := mkAppNBeta newCondition (originalConstrVars.map (mkFVar ·.fvarId))

          trace[Meta.debug] "NEW CONDITION {newCondition}"
          let fs := (collectFVars default newCondition).fvarIds
          for f in fs do 
            if let some idx := (originalConstrVars.map (·.fvarId)).getIdx? f then
              trace[Meta.debug] "found {idx}"
              vcondIdx := vcondIdx.push idx

          let newConditionTy ← inferType newCondition
          -- vcondIdx := vcondIdx.push (constraints.size + newConstraintsDecl.size)
          let localDecl := 
            LocalDecl.cdecl 0 (← mkFreshFVarId) `h newConditionTy Lean.BinderInfo.default LocalDeclKind.default
          newConstraints := newConstraints.push newCondition
          newConstraintsDecl := newConstraintsDecl.push localDecl
          -- throwError "Condition inference on vconditions not implemented"
        else 
          throwError "Variable condition {n} not found or inferred: \n {vcond} {constraints}."

    return (newConstraints, newConstraintsDecl, Tree.node vcondIdx childVCondIdxs)
  | Tree.leaf _, Tree.leaf _ => pure (#[], #[], Tree.leaf ())
  | _, _ => throwError "Tree mismatch."

/-- Returns the reduced expression and an array of forward images of new vars -/
partial def mkReducedWithSolution : Tree GraphAtomData Expr → MetaM (Tree (Expr × Array Expr) (Expr × Array Expr))
  | Tree.node atom childAtoms => do
    let mut childReducedExprs := #[]
    for i in [:childAtoms.size] do
      childReducedExprs := childReducedExprs.push $ ← mkReducedWithSolution childAtoms[i]!
    let sols := (atom.solution.map (mkAppNBeta · (childReducedExprs.1.map (·.val.1)).toArray))
    let reducedExpr := atom.impObjFun
    let reducedExpr := mkAppNBeta reducedExpr (childReducedExprs.1.map (·.val.1)).toArray
    let reducedExpr := mkAppNBeta reducedExpr sols
    return Tree.node (reducedExpr, sols) childReducedExprs
  | Tree.leaf e => pure $ Tree.leaf (e, #[])

/-- -/
def mkForwardImagesNewVars (reducedWithSolution : OC (Tree (Expr × Array Expr) (Expr × Array Expr))) : MetaM (Array Expr) := do
  let reducedWithSolutionTrees := #[reducedWithSolution.objFun] ++ reducedWithSolution.constr
  let mut fm := #[]
  for t in reducedWithSolutionTrees do
    fm := t.fold fm (fun acc a => Array.append acc a.2)
  trace[Meta.debug] "forwardImagesNewVars {fm}"
  return fm

/-- -/
partial def mkSolEqAtom : Tree GraphAtomData Expr → Tree (Expr × Array Expr) (Expr × Array Expr) → Tree (Array Expr) Unit → MetaM (Tree Expr Expr)
  | Tree.node atom childAtoms, Tree.node reducedWithSolution childReducedWithSolution, Tree.node vcondVars childVCondVars => do
    dbg_trace "HERE 1"
    -- Recursive calls for arguments.
    let mut childSolEqAtom := #[]
    for i in [:childAtoms.size] do
      childSolEqAtom := childSolEqAtom.push $
        ← mkSolEqAtom childAtoms[i]! childReducedWithSolution[i]! childVCondVars[i]!
    dbg_trace "HER 2"
    -- Rewrite arguments in atom expr.
    let mut solEqAtomR ← mkEqRefl atom.expr
    for c in childSolEqAtom do
      solEqAtomR ← mkCongr solEqAtomR c.val
    dbg_trace "HER 3"
    dbg_trace "{atom.vconds.size}"
    dbg_trace "{atom.vconds}"
    dbg_trace "{vcondVars.size}"
    dbg_trace "{vcondVars}"
    -- Use solEqAtom of children to rewrite the arguments in the vconditions.
    let mut vconds := #[]
    for i in [:vcondVars.size] do
      let mut vcondEqReducedVCond ← mkEqRefl atom.vconds[i]!.2
      for c in childSolEqAtom do
        vcondEqReducedVCond ← mkCongr vcondEqReducedVCond c.val
      vconds := vconds.push $ ← mkEqMPR vcondEqReducedVCond vcondVars[i]!
    dbg_trace "HER 4"
    -- Apply solEqAtom property of the atom.
    let solEqAtomL := atom.solEqAtom
    let solEqAtomL := mkAppN solEqAtomL (childReducedWithSolution.map (·.val.1))
    let solEqAtomL := mkAppN solEqAtomL vconds
    let solEqAtom ← mkEqTrans solEqAtomL solEqAtomR
    return Tree.node solEqAtom childSolEqAtom
  | Tree.leaf e, Tree.leaf _, Tree.leaf _ => do return Tree.leaf (← mkEqRefl e)
  | _, _, _ => throwError "Tree mismatch"

/-- -/
partial def mkFeasibility : Tree GraphAtomData Expr → Tree (Expr × Array Expr) (Expr × Array Expr) → Tree (Array Expr) Unit → Tree Expr Expr → MetaM (Tree (Array Expr) Unit)
| Tree.node atom childAtoms, Tree.node reducedWithSolution childReducedWithSolution, 
  Tree.node vcondVars childVCondVars, Tree.node solEqAtom childSolEqAtom => do
  -- Recursive calls for arguments.
  let mut childFeasibility := #[]
  for i in [:childAtoms.size] do
    let c ← mkFeasibility childAtoms[i]! childReducedWithSolution[i]! childVCondVars[i]! childSolEqAtom[i]!
    childFeasibility := childFeasibility.push c
  -- Use solEqAtom of children to rewrite the arguments in the vconditions.
  let mut vconds := #[]
  for i in [:vcondVars.size] do
    let mut vcondEqReducedVCond ← mkEqRefl atom.vconds[i]!.2
    for c in childSolEqAtom do
      vcondEqReducedVCond ← mkCongr vcondEqReducedVCond c.val
    vconds := vconds.push $ ← mkEqMPR vcondEqReducedVCond vcondVars[i]!
  -- Apply feasibility property of the atom.
  let feasibility := atom.feasibility
  let feasibility := feasibility.map (mkAppN · (childReducedWithSolution.map (·.val.1)))
  let feasibility := feasibility.map (mkAppN · vconds)
  let _ ← feasibility.mapM check
  return Tree.node feasibility childFeasibility
| Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _ => pure $ Tree.leaf ()
| _, _, _, _ => throwError "Tree mismatch"

/-- -/
partial def mkOptimalityAndVCondElim : Tree GraphAtomData Expr → Tree (Array Expr) Unit → 
    Tree Expr Expr → Tree (Array LocalDecl) Unit → 
    Tree (Array LocalDecl) Unit → Tree Curvature Curvature →
    Tree (Array Expr) (Array Expr) →
    MetaM (Tree (Expr × Array Expr) (Expr × Array Expr))
  | Tree.node atom childAtoms, Tree.node args childArgs, 
      Tree.node _reducedExpr childReducedExpr, Tree.node newVars childNewVars,
      Tree.node newConstrVars childNewConstrVars,
      Tree.node curvature childCurvature,
      Tree.node bconds childBConds => do
    trace[Meta.debug] "Optimality Start"
    -- Recursive calls for arguments.
    let mut childOptimality := #[]
    let mut childOptimalityFiltered := #[]
    for i in [:childAtoms.size] do
      if atom.argKinds[i]! != ArgKind.Constant ∧ atom.argKinds[i]! != ArgKind.Neither then
        let opt ← mkOptimalityAndVCondElim childAtoms[i]! childArgs[i]! childReducedExpr[i]!
            childNewVars[i]! childNewConstrVars[i]! childCurvature[i]! childBConds[i]!
        childOptimality := childOptimality.push opt
        childOptimalityFiltered := childOptimalityFiltered.push opt
      else
        childOptimality := childOptimality.push $ Tree.leaf (mkStrLit s!"dummy {args[i]!}", #[])
    let mut monoArgs := #[]
    for i in [:args.size] do
      if atom.argKinds[i]! != ArgKind.Constant ∧ atom.argKinds[i]! != ArgKind.Neither then
        monoArgs := monoArgs.push args[i]!

    -- Apply optimality property of atom.
    let optimality ←
      match curvature, atom.curvature with
      | Curvature.Concave, Curvature.Affine => mkAppM ``And.left #[atom.optimality]
      | Curvature.Convex, Curvature.Affine => mkAppM ``And.right #[atom.optimality]
      | _, _ => pure atom.optimality
    let optimality := mkAppN optimality (childReducedExpr.map Tree.val)
    let optimality := mkAppN optimality bconds
    check optimality
    let optimality := mkAppN optimality (newVars.map (mkFVar ·.fvarId))
    let optimality := mkAppN optimality (newConstrVars.map (mkFVar ·.fvarId))
    let optimality := mkAppN optimality monoArgs
    let optimality := mkAppN optimality (childOptimalityFiltered.map (·.val.1))
    check optimality

    -- Apply vcond elim property of atom.
    let vcondElim := atom.vcondElim
    let vcondElim := vcondElim.map (mkAppN · (childReducedExpr.map Tree.val))
    let vcondElim := vcondElim.map (mkAppN · (newVars.map (mkFVar ·.fvarId)))
    let vcondElim := vcondElim.map (mkAppN · (newConstrVars.map (mkFVar ·.fvarId)))
    let vcondElim := vcondElim.map (mkAppN · monoArgs)
    let vcondElim := vcondElim.map (mkAppN · (childOptimalityFiltered.map (·.val.1)))

    return Tree.node (optimality, vcondElim) childOptimality
  | Tree.leaf e, Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _ => do
    trace[Meta.debug] "Optimality Leaf {e}"
    return Tree.leaf (← mkAppM ``le_refl #[e], #[])
  | _, _, _, _, _, _, _ => throwError "Tree mismatch"

/-- -/
partial def mkNewConstrVars :  Tree (Array Expr) Unit → MetaM (Tree (Array LocalDecl) Unit)
| Tree.node newConstr childNewConstr => do
  -- Recursive calls for arguments
  let mut childNewConstrVar := #[]
  for i in [:childNewConstr.size] do
    childNewConstrVar := childNewConstrVar.push $
      ← mkNewConstrVars childNewConstr[i]!
  -- Create variables
  let mut newConstrVars : Array LocalDecl := #[]
  for ty in newConstr do
    newConstrVars := newConstrVars.push $
      LocalDecl.cdecl 0 (← mkFreshFVarId) `h ty Lean.BinderInfo.default LocalDeclKind.default
  return Tree.node newConstrVars childNewConstrVar
| Tree.leaf _ => pure $ Tree.leaf ()

/-- -/
def mkOriginalConstrVars (originalVarsDecls : Array LocalDecl) 
  (constr : Array (Lean.Name × Expr)) : MetaM (Array LocalDecl) := do
withExistingLocalDecls originalVarsDecls.toList do
  let mut decls : Array LocalDecl := #[]
  for i in [:constr.size] do
    decls := decls.push $ LocalDecl.cdecl 0 (← mkFreshFVarId) (Name.mkNum constr[i]!.1 i) constr[i]!.2 Lean.BinderInfo.default LocalDeclKind.default
  return decls

/-- -/
def mkVCondVars (originalConstrVars : Array FVarId) (vcondIdx : Tree (Array Nat) Unit) : Tree (Array Expr) Unit :=
  vcondIdx.map (fun is => is.map fun i => mkFVar originalConstrVars[i]!) id

/-- -/
def foldProdMk (exprs : Array Expr) : MetaM Expr := do
  if exprs.size == 0 then
    throwError "exprs cannot be empty"
  let mut res := exprs[exprs.size - 1]!
  for i in [1:exprs.size] do
    res ← mkAppM ``Prod.mk #[exprs[exprs.size - 1 - i]!, res]
  return res

/-- -/
def makeForwardMap (oldDomain : Expr) (xs : Array Expr) (forwardImagesNewVars : Array Expr): MetaM Expr := do
  withLocalDeclD `p oldDomain fun p => do
    let prs := (← Meta.mkProjections oldDomain p).map (·.2.2)
    let forwardBody := xs ++ forwardImagesNewVars
    let forwardMap ← mkLambdaFVars #[p] $ (← foldProdMk forwardBody).replaceFVars xs prs.toArray
    trace[Meta.debug] "forwardMap: {forwardMap}"
    check forwardMap
    return forwardMap

/-- -/
def makeBackwardMap (xs : Array Expr) (mkDomainFunc : Expr → MetaM Expr) : MetaM Expr := do
  let backwardBody ← foldProdMk $ xs
  let backwardMap ← mkDomainFunc backwardBody
  trace[Meta.debug] "backwardMap: {backwardMap}"
  check backwardMap
  trace[Meta.debug] "backwardMap checked"
  return backwardMap

/-- -/
def makeObjFunForward (oldDomain : Expr) (xs : Array Expr) (originalConstrVars : Array LocalDecl)
  (oldProblem : Expr) (constraints : Array Expr) (objFunEq : Expr) : MetaM Expr := do
  -- ∀ {x : D}, p.constraints x → q.objFun (f x) ≤ p.objFun x
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
      trace[Meta.debug] "objFunForward: {objFunForward}"
      check objFunForward
      return objFunForward

/-- -/
def foldAndIntro (exprs : Array Expr) : MetaM Expr := do
  if exprs.size == 0 then
    return mkConst ``True.intro
  let mut res := exprs[exprs.size - 1]!
  for i in [1:exprs.size] do
    res ← mkAppM ``And.intro #[exprs[exprs.size - 1 - i]!, res]
  return res

/-- -/
def makeConstrForward (oldDomain : Expr) (xs : Array Expr) (originalConstrVars vcondConstrVars : Array LocalDecl)
  (oldProblem : Expr) (constraints vcondNewConstraints : Array Expr) (isVCond : Array Bool) (constraintsEq : Array Expr)
  (feasibility : OC (Tree (Array Expr) Unit)) : MetaM Expr := do
  -- ∀ {x : D}, Minimization.constraints p x → Minimization.constraints q (f x)

  withLocalDeclD `p oldDomain fun p => do
    let prs := (← Meta.mkProjections oldDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[oldProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj constraints.toList
      let hProj := (cprs h).toArray

      -- let mut vcondNewConstraintsReplaced := #[] 
      -- for c in vcondNewConstraints do 
      --   let cReplaced := c.replaceFVars ((originalConstrVars).map (mkFVar ·.fvarId)) hProj
      --   vcondNewConstraintsReplaced := vcondNewConstraintsReplaced.push (← inferType cReplaced)
      -- let (_, cprs') := Meta.composeAndWithProj vcondNewConstraintsReplaced.toList
      -- let hProj' := (cprs' h).toArray

      -- trace[Meta.debug] "replaced: {vcondNewConstraintsReplaced}"
      -- trace[Meta.debug] "og varfs: {originalConstrVars.map (mkFVar ·.fvarId)}"

      -- Old constraint proofs.
      let mut oldConstrProofs := #[]
      for i in [:originalConstrVars.size] do
        if not isVCond[i]! then
          dbg_trace "constraintsEq : {constraintsEq[i]!}"
          -- NOTE(RFM): Is this right?
          oldConstrProofs := oldConstrProofs.push $
            ← mkAppM ``Eq.mpr #[constraintsEq[i]!, mkFVar originalConstrVars[i]!.fvarId]

      -- New constraint proofs.
      let newConstrProofs := feasibility.fold #[] fun acc fs => 
          fs.fold acc Array.append
      
      let constrForwardBody ← foldAndIntro $ (oldConstrProofs ++ newConstrProofs)
      let constrForwardBody := constrForwardBody.replaceFVars
        ((vcondConstrVars).map (mkFVar ·.fvarId)) vcondNewConstraints
      let constrForwardBody := constrForwardBody.replaceFVars
        ((originalConstrVars).map (mkFVar ·.fvarId)) hProj
      let constrForwardBody ← mkLambdaFVars #[h] constrForwardBody
      trace[Meta.debug] "constrForwardBody: {constrForwardBody}"

      let constrForwardBody := constrForwardBody.replaceFVars xs prs.toArray
      trace[Meta.debug] "constrForwardBody 2: {constrForwardBody}"
      let constrForward ← mkLambdaFVars #[p] constrForwardBody
      trace[Meta.debug] "constrForward: {constrForward}"
      trace[Meta.debug] "constrForwardType: {← inferType constrForward}"
      check constrForward
      trace[Meta.debug] "HERE"
      return constrForward

/-- -/
def makeObjFunBackward (newDomain : Expr) (newProblem : Expr) (xs : Array Expr) (ys : Array Expr) (objFunOpt : Expr)
    (reducedConstrs : Array Expr) (newConstrs : Array Expr)
    (newConstrVars : Array LocalDecl) : MetaM Expr := do
  -- ∀ {x : E}, Minimization.constraints q x → Minimization.objFun p (g x) ≤ Minimization.objFun q x

  withLocalDeclD `p newDomain fun p => do
    let prs := (← Meta.mkProjections newDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[newProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj (reducedConstrs ++ newConstrs).toList
      let hProj := cprs h
      let objFunBackwardBody := objFunOpt
      let objFunBackwardBody := objFunBackwardBody.replaceFVars
        (newConstrVars.map (mkFVar ·.fvarId)) (hProj.drop (hProj.length - newConstrVars.size)).toArray
      let objFunBackwardBody := objFunBackwardBody.replaceFVars
        (xs ++ ys) prs.toArray
      let objFunBackward ← mkLambdaFVars #[p, h] objFunBackwardBody
      trace[Meta.debug] "objFunBackward: {objFunBackward}"
      check objFunBackward
      return objFunBackward

/-- -/
def makeConstrBackward (vcondElimMap : Std.HashMap Nat Expr) (newDomain : Expr) (newProblem : Expr) (xs : Array Expr) (ys : Array Expr) (constrOpt : Array Expr)
    (reducedConstrs : Array Expr) (newConstrs : Array Expr) (newConstrVars : Array LocalDecl) : MetaM Expr := do
  -- ∀ {x : E}, Minimization.constraints q x → Minimization.constraints p (g x)

  withLocalDeclD `p newDomain fun p => do
    let prs := (← Meta.mkProjections newDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[newProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj (reducedConstrs ++ newConstrs).toList
      let hProj := cprs h
      let mut constrBackwardProofs := #[]
      let mut filteredCounter := 0
      for i in [:constrOpt.size] do
        match vcondElimMap.find? i with
        | some p => 
          constrBackwardProofs := constrBackwardProofs.push $ p
        | none => 
          constrBackwardProofs := constrBackwardProofs.push $ mkApp constrOpt[i]! hProj.toArray[filteredCounter]!
          filteredCounter := filteredCounter + 1
      
      let constrBackwardBody ← foldAndIntro constrBackwardProofs

      let constrBackwardBody := constrBackwardBody.replaceFVars
        (newConstrVars.map (mkFVar ·.fvarId)) (hProj.drop (hProj.length - newConstrVars.size)).toArray

      let constrBackwardBody := constrBackwardBody.replaceFVars
        (xs ++ ys) prs.toArray

      let constrBackward ← mkLambdaFVars #[p, h] constrBackwardBody
      trace[Meta.debug] "constrBackward: {constrBackward}"
      check constrBackward
      return constrBackward

/-- Extract objective and constraints in terms of the optimization variables. -/
def mkOC (objFun : Expr) (constraints : List (Lean.Name × Expr)) (originalVarsDecls : Array LocalDecl)
  : MetaM (OC Expr) := do
  withExistingLocalDecls originalVarsDecls.toList do
    let oc := OC.mk objFun (constraints.toArray.map (fun (c : Lean.Name × Expr) => c.2))
    return oc

/-- Same as `mkOC` but keeping constraint tags. The objective function is tagged
with anonymous. -/
def mkOCWithNames (objFun : Expr) (constraints : List (Lean.Name × Expr)) (originalVarsDecls : Array LocalDecl)
  : MetaM (OC (Lean.Name × Expr)) := do
  withExistingLocalDecls originalVarsDecls.toList do
    let oc := OC.mk (`_, objFun) constraints.toArray
    return oc

-- TODO: Better error message when discovering a concave atom where convex is expected, and vice versa.
/-- Construct the atom tree. -/
def mkAtomTree (originalVarsDecls : Array LocalDecl) (oc : OC Expr) : 
  MetaM (
    OC Bool ×  
    OC (Array MessageData) × 
    OC (Tree GraphAtomData Expr) × 
    OC (Tree (Array Expr) Unit) × 
    OC (Tree Curvature Curvature) × 
    OC (Tree (Array Expr) (Array Expr))) := do
withExistingLocalDecls originalVarsDecls.toList do
  let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
  -- Find atoms.
  let atomsAndArgs ← OC.map2M (fun e c => findAtoms e (xs.map (·.fvarId!)) c) oc 
    ⟨Curvature.Convex, oc.constr.map (fun _ => Curvature.Concave)⟩
  let failedAtom : OC Bool := atomsAndArgs.map (·.fst)
  let failedAtomMsgs : OC (Array MessageData) := atomsAndArgs.map (·.snd.fst)
  if failedAtom.objFun then
    throwError "Failure in objective: {failedAtomMsgs.objFun}"
  
  let atoms := atomsAndArgs.map (·.snd.snd.fst)
  let args := atomsAndArgs.map (·.snd.snd.snd.fst)
  let curvature := atomsAndArgs.map (·.snd.snd.snd.snd.fst)
  let bconds := atomsAndArgs.map (·.snd.snd.snd.snd.snd)
  return (failedAtom, failedAtomMsgs, atoms, args, curvature, bconds)

/-- Identify vconditions and check that all failed constraints can be used as 
vconditions. -/
def mkVConditions (originalVarsDecls : Array LocalDecl) (oc : OC Expr)
  (constraints : List (Lean.Name × Expr)) (atoms : OC (Tree GraphAtomData Expr)) (args : OC (Tree (Array Expr) Unit)) 
  (failedAtom : OC Bool) (failedAtomMsgs : OC (Array MessageData)) (originalConstrVars : Array LocalDecl) :
  MetaM ((Array Expr) × (Array LocalDecl) × OC (Tree (Array ℕ) Unit) × Array Bool × OC (Tree (Array Expr) Unit)) := do
withExistingLocalDecls originalVarsDecls.toList do
  let vcondResult ← OC.map2M (findVConditions originalConstrVars oc.constr #[] #[]) atoms args
  let vcondNewConstrs := (vcondResult.map (·.1)).fold #[] fun acc cs => acc ++ cs
  let vcondNewConstrsDecl := (vcondResult.map (·.2.1)).fold #[] fun acc cs => acc ++ cs
  let vcondIdx := vcondResult.map (·.2.2)

  trace[Meta.debug] "vcondIdx {vcondIdx}"
  let isVCond := vcondIdx.fold ((originalConstrVars ++ vcondNewConstrsDecl).map (fun _ => false)) 
    fun acc vcondIdxTree =>
      vcondIdxTree.fold acc fun acc is => 
        is.foldl (fun acc i => acc.set! i true) acc
  let vcondVars := vcondResult.map <| fun (_, newDecls, idx) => 
    mkVCondVars ((originalConstrVars ++ newDecls).map LocalDecl.fvarId) idx
  
  trace[Meta.debug] "isVCond: {isVCond}"
  for i in [:isVCond.size] do
    trace[Meta.debug] "{constraints.toArray[i]!.1} is vcond? {isVCond[i]!}"
    if failedAtom.constr[i]! ∧ ¬ isVCond[i]! then
      trace[Meta.debug] "Failure in constraint {constraints.toArray[i]!.1}: {failedAtomMsgs.constr[i]!}"
  return (vcondNewConstrs, vcondNewConstrsDecl, vcondIdx, isVCond, vcondVars)

/-- -/
def mkSolEqAtomOC (originalVarsDecls : Array LocalDecl) 
  (atoms : OC (Tree GraphAtomData Expr)) (reducedWithSolution : OC (Tree (Expr × Array Expr) (Expr × Array Expr)))
  (vcondVars : OC (Tree (Array Expr) Unit)) (originalConstrVars : Array LocalDecl) : MetaM (OC (Tree Expr Expr)) :=
withExistingLocalDecls originalVarsDecls.toList do
  withExistingLocalDecls originalConstrVars.toList do
    let solEqAtom ← OC.map3M mkSolEqAtom atoms reducedWithSolution vcondVars
    trace[Meta.debug] "solEqAtom {solEqAtom}"
    return solEqAtom

/-- -/
def mkFeasibilityOC (originalVarsDecls : Array LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr)) (reducedWithSolution : OC (Tree (Expr × Array Expr) (Expr × Array Expr)))
  (vcondVars : OC (Tree (Array Expr) Unit)) (originalConstrVars : Array LocalDecl) (solEqAtom : OC (Tree Expr Expr)) :
  MetaM (OC (Tree (Array Expr) Unit)) :=
withExistingLocalDecls originalVarsDecls.toList do
  withExistingLocalDecls originalConstrVars.toList do
    let feasibility ← OC.map4M mkFeasibility atoms reducedWithSolution vcondVars solEqAtom
    trace[Meta.debug] "feasibility {feasibility}"
    return feasibility
/-- -/
def mkReducedExprsOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr)) (newVars : OC (Tree (Array LocalDecl) Unit)) : MetaM (OC (Tree Expr Expr)) :=
withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
        let reducedExprs ← OC.map2M mkReducedExprs atoms newVars
        trace[Meta.debug] "reducedExprs {reducedExprs}"
        return reducedExprs

/-- -/
def mkNewConstrsOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
 (atoms : OC (Tree GraphAtomData Expr)) (newVars : OC (Tree (Array LocalDecl) Unit)) (reducedExprs : OC (Tree Expr Expr)) 
 : MetaM (Array Expr × OC (Tree (Array LocalDecl) Unit) × Array LocalDecl):=
withExistingLocalDecls (originalVarsDecls.toList) do
  withExistingLocalDecls newVarDecls do
    let newConstrs ← OC.map3M mkNewConstrs atoms newVars reducedExprs
    trace[Meta.debug] "newConstrs {newConstrs}"
    let newConstrVars ← OC.mapM mkNewConstrVars newConstrs
    trace[Meta.debug] "newConstrs {newConstrs}"
    let newConstrs : Array Expr := newConstrs.fold #[] fun acc cs => 
      cs.fold acc Array.append
    let newConstrVarsArray : Array LocalDecl := newConstrVars.fold #[] fun acc cs => 
      cs.fold acc Array.append
    return (newConstrs, newConstrVars, newConstrVarsArray)

/-- -/
def mkOptimalityAndVCondElimOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
  (newConstrVarsArray : Array LocalDecl) (atoms : OC (Tree GraphAtomData Expr)) (args : OC (Tree (Array Expr) Unit))
  (reducedExprs : OC (Tree Expr Expr)) (newVars : OC (Tree (Array LocalDecl) Unit)) (newConstrVars : OC (Tree (Array LocalDecl) Unit))
  (curvature : OC (Tree Curvature Curvature)) (bconds : OC (Tree (Array Expr) (Array Expr))) (vcondIdx : OC (Tree (Array ℕ) Unit))
  : MetaM (OC (Tree Expr Expr) × Std.HashMap ℕ Expr):=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
      withExistingLocalDecls newConstrVarsArray.toList do
        let optimalityAndVCondElim ← OC.map7M mkOptimalityAndVCondElim atoms args reducedExprs newVars newConstrVars curvature bconds
        let optimality := optimalityAndVCondElim.map (fun oce => oce.map Prod.fst Prod.fst)
        let vcondElim := optimalityAndVCondElim.map (fun oce => oce.map Prod.snd Prod.snd)
        trace[Meta.debug] "optimality {optimality}"
        trace[Meta.debug] "vcondElim {vcondElim}"

        let vcondElimWithIdx ← OC.map2M (fun a b => Tree.zip a b) vcondIdx vcondElim
        let vcondElimMap := vcondElimWithIdx.fold {}
          fun (map : Std.HashMap Nat Expr) ci => 
            ci.fold map fun (map : Std.HashMap Nat Expr) ci => Id.run do
              let mut res := map
              for i in [:ci.1.size] do
                res := res.insert ci.1[i]! ci.2[i]!
              return res
        return (optimality, vcondElimMap)

/-- -/
structure ProcessedAtomTree where
  (originalVarsDecls : Array LocalDecl) 
  (originalConstrVars : Array LocalDecl) 
  (newVarDecls : List LocalDecl) 
  (newConstrs : Array Expr) 
  (newConstrVarsArray : Array LocalDecl) 
  (forwardImagesNewVars : Array Expr) 
  (constraints : List (Lean.Name × Expr))
  (vcondNewConstrs : Array Expr)
  (vcondNewConstrsVars : Array LocalDecl)
  (isVCond : Array Bool) 
  (vcondElimMap : Std.HashMap ℕ Expr)
  (solEqAtom : OC (Tree Expr Expr)) 
  (feasibility : OC (Tree (Array Expr) Unit)) 
  (reducedExprs : OC (Tree Expr Expr)) 
  (optimality : OC (Tree Expr Expr))

/-- -/
def mkProcessedAtomTree (objFun : Expr) (constraints : List (Lean.Name × Expr)) (originalVarsDecls : Array LocalDecl)
  : MetaM ProcessedAtomTree := do
  let oc ← mkOC objFun constraints originalVarsDecls
  let (failedAtom, failedAtomMsgs, atoms, args, curvature, bconds) ← mkAtomTree originalVarsDecls oc
  let originalConstrVars ← mkOriginalConstrVars originalVarsDecls constraints.toArray
  dbg_trace "initial list: {originalConstrVars.size}"
  let (vcondNewConstrs, vcondNewConstrsVars, vcondIdx, isVCond, vcondVars) ← mkVConditions originalVarsDecls oc constraints atoms args failedAtom
    failedAtomMsgs originalConstrVars
  trace[Meta.debug] "vcondNewConstrs {vcondNewConstrs}"

  let newVars ← withExistingLocalDecls originalVarsDecls.toList do
    OC.map2MwithCounter mkNewVars atoms args
  let newVarDecls ← mkNewVarDeclList newVars
  let reducedWithSolution ← withExistingLocalDecls originalVarsDecls.toList do
    OC.mapM mkReducedWithSolution atoms
  let forwardImagesNewVars ← withExistingLocalDecls originalVarsDecls.toList do
    mkForwardImagesNewVars reducedWithSolution
  

  let solEqAtom ← mkSolEqAtomOC originalVarsDecls atoms reducedWithSolution vcondVars originalConstrVars
  let feasibility ← mkFeasibilityOC originalVarsDecls atoms reducedWithSolution vcondVars 
    (originalConstrVars ++ vcondNewConstrsVars) solEqAtom
  let reducedExprs ← mkReducedExprsOC originalVarsDecls newVarDecls atoms newVars
  let (newConstrs, newConstrVars, newConstrVarsArray)
    ← mkNewConstrsOC originalVarsDecls newVarDecls atoms newVars reducedExprs
  let (optimality, vcondElimMap) ← mkOptimalityAndVCondElimOC originalVarsDecls newVarDecls
    (newConstrVarsArray ++ vcondNewConstrsVars) atoms args reducedExprs newVars newConstrVars curvature bconds vcondIdx
  
  return ProcessedAtomTree.mk
    (originalVarsDecls := originalVarsDecls) 
    (originalConstrVars := originalConstrVars) 
    (newVarDecls := newVarDecls) 
    (newConstrs := newConstrs) 
    (newConstrVarsArray := newConstrVarsArray) 
    (forwardImagesNewVars := forwardImagesNewVars) 
    (constraints := constraints)
    (vcondNewConstrs := vcondNewConstrs)
    (vcondNewConstrsVars := vcondNewConstrsVars)
    (isVCond := isVCond) 
    (vcondElimMap := vcondElimMap)
    (solEqAtom := solEqAtom) 
    (feasibility := feasibility) 
    (reducedExprs := reducedExprs) 
    (optimality := optimality)

/-- -/
-- NOTE: Temporarily changing this to not only return the map from 
-- solution to solution but also the forward and backward maps. 
-- TODO: Better types for return type.
def canonizeGoalFromSolutionExpr (goalExprs : Meta.SolutionExpr) : 
  MetaM (Expr × (Expr × Expr × Expr)) := do
  -- Extract objective and constraints from `goalExprs`.
  let (objFun, constraints, originalVarsDecls)
    ← withLambdaBody goalExprs.constraints fun p constraints => do
    let pr := (← Meta.mkProjections goalExprs.domain p).toArray
    let originalVarsDecls ←
      withLocalDeclsD (pr.map fun (n, ty, _) => (n, fun _ => return ty)) 
        fun xs => do
          return ← xs.mapM fun x => x.fvarId!.getDecl
    withExistingLocalDecls originalVarsDecls.toList do
      let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
      let constraints ← Meta.replaceProjections constraints p.fvarId! xs
      let constraints : List (Lean.Name × Expr) ← 
        Meta.decomposeConstraints constraints
      let constraints ← 
        constraints.mapM (fun ((n : Lean.Name), e) => do 
          return (n, ← Expr.removeMData e))
      let objFunP := goalExprs.objFun.bindingBody!.instantiate1 p
      let objFun ← Meta.replaceProjections objFunP p.fvarId! xs
      return (objFun, constraints, originalVarsDecls)

  -- Process the atom tree.
  let pat ← mkProcessedAtomTree objFun constraints originalVarsDecls

  -- Create new goal and reduction.
  let (forwardMap, backwardMap, reduction) ← withExistingLocalDecls pat.originalVarsDecls.toList do
      let xs := pat.originalVarsDecls.map fun decl => mkFVar decl.fvarId
    
      let forwardMap ← makeForwardMap goalExprs.domain xs pat.forwardImagesNewVars
      
      let activeConstrVars := pat.originalConstrVars ++ pat.vcondNewConstrsVars
      let (objFunForward, constrForward) ← 
        withExistingLocalDecls activeConstrVars.toList do

          let activeConstrs := (pat.constraints.toArray.map Prod.snd) ++ pat.vcondNewConstrs.toList
          dbg_trace "activeConstrs {activeConstrs.size}"
          dbg_trace "activeConstrVars {activeConstrVars.size}"

          let objFunForward ← makeObjFunForward goalExprs.domain xs activeConstrVars goalExprs.toMinimizationExpr.toExpr
            activeConstrs pat.solEqAtom.objFun.val
          let constrForward ← makeConstrForward goalExprs.domain xs 
            pat.originalConstrVars pat.vcondNewConstrsVars -- decls 
            goalExprs.toMinimizationExpr.toExpr 
            (pat.constraints.toArray.map Prod.snd) pat.vcondNewConstrs -- constraints 
            pat.isVCond 
            (pat.solEqAtom.constr.map Tree.val) 
            pat.feasibility
          
          return (objFunForward, constrForward)

      withExistingLocalDecls pat.newVarDecls do
        let ys := (pat.newVarDecls.map (mkFVar ·.fvarId)).toArray
        trace[Meta.debug] "ys: {ys}"

        let vars ← (xs ++ ys).mapM fun x => do 
          let decl ← x.fvarId!.getDecl
          return (decl.userName, decl.type)
        let newDomain := Meta.composeDomain vars.toList
        let mkDomainFunc := fun e =>
          withLocalDeclD `p newDomain fun p => do
            let prs := (← Meta.mkProjections newDomain p).map (·.2.2)
            let e := Expr.replaceFVars e (xs ++ ys) prs.toArray
            mkLambdaFVars #[p] e

        let reducedConstrs := pat.reducedExprs.constr.map Tree.val
        let reducedConstrs := reducedConstrs.filterIdx (fun i => ¬ pat.isVCond[i]!)

        let newProblem : Meta.SolutionExpr := { goalExprs with
          domain := newDomain
          domain' := newDomain
          objFun := ← mkDomainFunc pat.reducedExprs.objFun.val
          constraints := ← mkDomainFunc $ Meta.composeAnd (reducedConstrs ++ pat.newConstrs).toList
        }
        let newProblemExpr := newProblem.toExpr

        let backwardMap ← makeBackwardMap xs mkDomainFunc

        let (objFunBackward, constrBackward) ← 
          withExistingLocalDecls pat.newConstrVarsArray.toList do
            let objFunBackward ← makeObjFunBackward newDomain newProblem.toMinimizationExpr.toExpr xs ys pat.optimality.objFun.val
              reducedConstrs pat.newConstrs pat.newConstrVarsArray
            
            let constrBackward ← makeConstrBackward pat.vcondElimMap newDomain newProblem.toMinimizationExpr.toExpr xs ys (pat.optimality.constr.map (·.val))
              reducedConstrs pat.newConstrs pat.newConstrVarsArray

            return (objFunBackward, constrBackward)

        let res ← mkAppM ``Minimization.simple_reduction #[goalExprs.toMinimizationExpr.toExpr, newProblem.toMinimizationExpr.toExpr]
        check res
        
        let res := mkApp res (mkBVar 0) -- Insert new goal here later.
        let res := mkApp6 res
          forwardMap
          backwardMap
          objFunForward
          objFunBackward
          constrForward
          constrBackward
        let res := mkLambda `sol Lean.BinderInfo.default newProblemExpr res

        check res
        let res ← instantiateMVars res
        return (forwardMap, backwardMap, res)
    
  let newGoal ← mkFreshExprMVar none

  return (newGoal, (forwardMap, backwardMap, reduction))

/-- -/
def canonizeGoalFromExpr (goalExpr : Expr) : MetaM (Expr × (Expr × Expr × Expr)) := do 
  let goalExprs ← Meta.SolutionExpr.fromExpr goalExpr
  canonizeGoalFromSolutionExpr goalExprs

/-- -/
def canonizeGoal (goal : MVarId) : MetaM MVarId := do
  let goalExprs ← Meta.SolutionExpr.fromGoal goal
  let (newGoal, (_forwardMap, _backwardMap, reduction)) ← canonizeGoalFromSolutionExpr goalExprs
  let assignment := mkApp reduction newGoal
  check assignment
  goal.assign assignment
  return newGoal.mvarId!

end DCP

namespace Tactic

open Lean.Elab Lean.Elab.Tactic

syntax (name := dcp) "dcp" : tactic

@[tactic dcp]
def evalDcp : Tactic := fun stx => match stx with
| `(tactic| dcp) => do
  let goal ← Elab.Tactic.getMainGoal
  replaceMainGoal [← DCP.canonizeGoal goal]
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
