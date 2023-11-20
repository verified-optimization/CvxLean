import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Syntax.Minimization
import CvxLean.Meta.Util.Meta
import CvxLean.Lib.Math.Data.Array
import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.DCP.OC
import CvxLean.Meta.Util.Expr
import CvxLean.Tactic.Solver.Float.OptimizationParam

namespace CvxLean

open Lean Lean.Meta

namespace DCP

abbrev GraphAtomDataTree := Tree GraphAtomData Expr

abbrev Argument := Expr
abbrev Arguments := Array Argument
abbrev ArgumentsTree := Tree Arguments Unit

abbrev CurvatureTree := Tree Curvature Curvature

abbrev BCond := Expr
abbrev BConds := Array BCond
abbrev BCondsTree := Tree BConds BConds

abbrev AtomDataTrees :=
  GraphAtomDataTree × ArgumentsTree × CurvatureTree × BCondsTree

abbrev NewVarsTree := Tree (Array LocalDecl) Unit
abbrev NewConstrVarsTree := Tree (Array LocalDecl) Unit

/-- TODO Check if `expr` is constant by checking if it contains any free variable
from `vars`. -/
def isConstant (expr : Expr) : Bool := (collectFVars {} expr).fvarSet.isEmpty

/-- Check if `expr` is constant by checking if it contains any free variable
from `vars`. -/
def isRelativelyConstant (expr : Expr) (vars : Array FVarId) : Bool := Id.run do
  let fvarSet := (collectFVars {} expr).fvarSet
  for v in vars do
    if fvarSet.contains v then return false
  return true

/-- Return list of all registered atoms that match with a given expression.
For every registered atom, it returns:
* The list of arguments as Lean expressions for further matching.
* The atom entry, of type `GraphAtomData`. -/
def findRegisteredAtoms (e : Expr) :
  MetaM (Array (Arguments × GraphAtomData)) := do
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
  -- Heuristic sorting of potential atoms to use: larger expressions have priority.
  goodAtoms := goodAtoms.insertionSort (fun a b => (a.2.expr.size - b.2.expr.size != 0))
  return goodAtoms

/-- Data type used to indicate whether an atom could be successfully
processed. It is used by `processAtom`. A successful match includes 4 trees:
* A tree of atom data (see `GraphAtomData`).
* A tree of arguments for every node.
* A tree of curvatures.
* A tree of background conditions.
-/
inductive FindAtomResult
| Success (res : AtomDataTrees)
| Error (msgs : Array MessageData)

/-- Given an expression `e`, optimization variables `vars` and the expected
curvature `curvature`, this function attempts to recursively match `e` with
atoms for the library outputing all the necessary information as explained
in `FindAtomResult`. The boolean in the output indicates whether a match from
the library was used. -/
partial def findAtoms (e : Expr) (vars : Array FVarId) (curvature : Curvature) :
  MetaM (
    Bool ×
    Array MessageData ×
    AtomDataTrees) := do
  trace[Meta.debug] "Constant? {e} {vars.map (mkFVar ·)}"
  if isRelativelyConstant e vars || curvature == Curvature.Constant then
    trace[Meta.debug] "Yes"
    return (false, #[], Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
  if e.isFVar then --∧ vars.contains e.fvarId! then
    trace[Meta.debug] "Variable {e}"
    return (false, #[], Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
  let potentialAtoms ← findRegisteredAtoms e
  let mut failedAtoms : Array MessageData := #[]
  if potentialAtoms.size == 0 then
    failedAtoms := failedAtoms.push m!"No atom found for {e}"
  for (args, atom) in potentialAtoms do
    match ← processAtom e vars curvature atom args with
    | FindAtomResult.Success (atoms, args, curvatures, bconds) =>
        trace[Meta.debug] "Success {e} : {atom}"
        return (false, failedAtoms, atoms, args, curvatures, bconds)
    | FindAtomResult.Error msg =>
        failedAtoms := failedAtoms ++ msg
  return (true, failedAtoms, Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
where
  processAtom (e : Expr) (vars : Array FVarId) (curvature : Curvature) (atom : GraphAtomData) (args : Array Expr) : MetaM FindAtomResult := do
    trace[Meta.debug] "Processing atom {atom.expr} for expression {e}, curvature {curvature}"
    -- TODO: is this correct?
    if atom.curvature != Curvature.Affine ∧ curvature != atom.curvature then
      return FindAtomResult.Error
        #[m!"Trying atom {atom.expr} for expression {e}: " ++
          m!"Expected {curvature}, but atom is {atom.curvature}"]
    let mut abort := false -- TODO: use exception instead?
    let mut bconds := #[]
    for (bcondName, bcondType) in atom.bconds do
      let bcondType := mkAppNBeta bcondType args
      let fvarId? ← (← getLCtx).decls.findSomeM? fun decl => match decl with
        | none => pure none
        | some decl => do
          if ← isDefEq decl.type bcondType then return some decl.fvarId else return none
      match fvarId? with
      | some fvarId =>
        bconds := bconds.push (mkFVar fvarId)
      | none =>
        -- Try to prove simple bconditions by norm_num.
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
      if atom.argKinds[i]! == ArgKind.Constant ∧ not (isRelativelyConstant arg vars) then
        return FindAtomResult.Error
          #[m!"Trying atom {atom.expr} for expression {e}: " ++
            m!"Expected constant argument, but found: {arg}"]
      let c := curvatureInArg curvature atom.argKinds[i]!
      trace[Meta.debug] "Trying to find atoms for {arg} with curvature {c}"
      trace[Meta.debug] "vars: {vars.map (mkFVar ·)}"
      trace[Meta.debug] "args: {args}"
      let (childFailed, childFailedAtoms, childTree, childArgsTree, childCurvature, childBCond) ← findAtoms arg vars c
      if childFailed then
        return FindAtomResult.Error childFailedAtoms
      trace[Meta.debug] "Found {childTree}"
      childTrees := childTrees.push childTree
      childArgsTrees := childArgsTrees.push childArgsTree
      childCurvatures := childCurvatures.push childCurvature
      childBConds := childBConds.push childBCond
    if curvature == Curvature.Affine then
      trace[Meta.debug] "Affine branch for {e}"
      -- For affine branches, we only check that all atoms are affine, but don't store the results.
      return FindAtomResult.Success (Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf bconds)
    else
      return FindAtomResult.Success (Tree.node atom childTrees, Tree.node args childArgsTrees, Tree.node curvature childCurvatures, Tree.node bconds childBConds)

/-- Returns number of added variables -/
partial def mkNewVars (i : Nat) : GraphAtomDataTree → ArgumentsTree → MetaM (NewVarsTree × Nat)
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
def mkNewVarDeclList (newVars : OC NewVarsTree) :
  MetaM (List LocalDecl) := do
  let newVarTrees := #[newVars.objFun] ++ newVars.constr
  let mut newVarDecls := #[]
  for t in newVarTrees do
    newVarDecls := t.fold newVarDecls Array.append
  return newVarDecls.toList

abbrev ReducedExpr := Expr
abbrev ReducedExprsTree := Tree ReducedExpr ReducedExpr

/-- -/
partial def mkReducedExprs : GraphAtomDataTree → NewVarsTree → MetaM (Tree Expr Expr)
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

abbrev NewConstrsTree := Tree (Array Expr) Unit

/-- -/
partial def mkNewConstrs : GraphAtomDataTree → NewVarsTree → ReducedExprsTree → MetaM NewConstrsTree
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


abbrev PreVCond := ℕ ⊕ Expr
abbrev PreVConds := Array PreVCond
abbrev PreVCondsTree := Tree PreVConds Unit

abbrev VCond := Expr
abbrev VConds := Array VCond
abbrev VCondsTree := Tree VConds Unit

/-- Returns index of constraint if vcondition corresponds exactly to a constraint
(this is needed for condition elimination). If not, it tries to deduce the condition
from other constraints and returns an expression. -/
partial def findVConditions (originalConstrVars : Array LocalDecl) (constraints : Array Expr) :
  GraphAtomDataTree → ArgumentsTree → MetaM PreVCondsTree
  | Tree.node atom childAtoms, Tree.node args childArgs => do
    let mut childrenVCondData := #[]
    for i in [:childAtoms.size] do
      let childVCondData ←
        findVConditions originalConstrVars constraints childAtoms[i]! childArgs[i]!
      childrenVCondData := childrenVCondData.push childVCondData
    let mut vcondData := #[]
    for (n, vcond) in atom.vconds do
      let vcond := mkAppNBeta vcond args

      -- First, try to see if it matches exactly with any of the constraints.
      match ← constraints.findIdxM? (isDefEq vcond) with
      | some i => do vcondData := vcondData.push (Sum.inl i)
      | none =>
        -- TODO(RFM): Same issue with background conditions. Find a less hacky way?
        -- Infer vconditions from constraints.
        let vcondProofTyBody ← liftM <| constraints.foldrM mkArrow vcond
        let vcondProofTy ← mkForallFVars args vcondProofTyBody

        let (e, _) ← Lean.Elab.Term.TermElabM.run <| Lean.Elab.Term.commitIfNoErrors? <| do
            let tac ← `(by intros; try { norm_num <;> positivity <;> linarith })
            let v ← Lean.Elab.Term.elabTerm tac.raw (some vcondProofTy)
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars v

        if let some e' := e then
          -- The inferred variable condition.
          let newCondition := mkAppNBeta e' args
          let newCondition := mkAppNBeta newCondition (originalConstrVars.map (mkFVar ·.fvarId))

          vcondData := vcondData.push (Sum.inr newCondition)
        else
          throwError "Variable condition {n} not found or inferred: \n {vcond} {constraints}."

    return (Tree.node vcondData childrenVCondData)
  | Tree.leaf _, Tree.leaf _ => pure (Tree.leaf ())
  | _, _ => throwError "Tree mismatch."

-- One variable
abbrev NewVarAssignment := Expr

abbrev Solution := Array NewVarAssignment

structure ReducedExprWithSolution where
  reducedExpr : ReducedExpr
  solution : Solution

instance : Inhabited ReducedExprWithSolution := ⟨⟨default, default⟩⟩

abbrev ReducedExprsWithSolutionTree := Tree ReducedExprWithSolution ReducedExprWithSolution

/-- Returns the reduced expression and an array of forward images of new vars -/
partial def mkReducedWithSolution : GraphAtomDataTree → MetaM ReducedExprsWithSolutionTree
  | Tree.node atom childAtoms => do
      let mut childReducedExprs := #[]
      for i in [:childAtoms.size] do
        childReducedExprs := childReducedExprs.push $ ← mkReducedWithSolution childAtoms[i]!
      let sols := (atom.solution.map (mkAppNBeta · (childReducedExprs.1.map (·.val.1)).toArray))
      let reducedExpr := atom.impObjFun
      let reducedExpr := mkAppNBeta reducedExpr (childReducedExprs.1.map (·.val.1)).toArray
      let reducedExpr := mkAppNBeta reducedExpr sols
      return Tree.node ⟨reducedExpr, sols⟩  childReducedExprs
  | Tree.leaf e =>
      return Tree.leaf ⟨e, #[]⟩

/-- Combine all the solutions introduced by every atom expansion. A solution
tells us how to assign new variables from old ones. Here, we collect all such
assignments, which will be used later on to build the forward map between the
original and reduced problems. -/
def mkForwardImagesNewVars (reducedWithSolution : OC ReducedExprsWithSolutionTree) : MetaM Solution := do
  let reducedWithSolutionTrees := #[reducedWithSolution.objFun] ++ reducedWithSolution.constr
  let mut fm := #[]
  for t in reducedWithSolutionTrees do
    fm := t.fold fm (fun acc a => Array.append acc a.solution)
  trace[Meta.debug] "forwardImagesNewVars {fm}"
  return fm

abbrev SolEqAtomProof := Expr
abbrev SolEqAtomProofsTree := Tree SolEqAtomProof SolEqAtomProof

/-- Proofs .-/
partial def mkSolEqAtom :
  GraphAtomDataTree →
  ReducedExprsWithSolutionTree →
  VCondsTree →
  MetaM SolEqAtomProofsTree
  | Tree.node atom childAtoms,
    Tree.node reducedWithSolution childReducedWithSolution,
    Tree.node vcondVars childVCondVars => do
      -- Recursive calls for arguments.
      let mut childSolEqAtom := #[]
      for i in [:childAtoms.size] do
        childSolEqAtom := childSolEqAtom.push $
          ← mkSolEqAtom childAtoms[i]! childReducedWithSolution[i]! childVCondVars[i]!
      -- Rewrite arguments in atom expr.
      let mut solEqAtomR ← mkEqRefl atom.expr
      for c in childSolEqAtom do
        solEqAtomR ← mkCongr solEqAtomR c.val
      -- Use solEqAtom of children to rewrite the arguments in the vconditions.
      let mut vconds := #[]
      for i in [:vcondVars.size] do
        let mut vcondEqReducedVCond ← mkEqRefl atom.vconds[i]!.2
        for c in childSolEqAtom do
          vcondEqReducedVCond ← mkCongr vcondEqReducedVCond c.val
        vconds := vconds.push $ ← mkEqMPR vcondEqReducedVCond vcondVars[i]!
      -- Apply solEqAtom property of the atom.
      let solEqAtomL := atom.solEqAtom
      let solEqAtomL := mkAppN solEqAtomL (childReducedWithSolution.map (·.val.1))
      let solEqAtomL := mkAppN solEqAtomL vconds
      let solEqAtom ← mkEqTrans solEqAtomL solEqAtomR
      return Tree.node solEqAtom childSolEqAtom
  | Tree.leaf e, Tree.leaf _, Tree.leaf _ => do
      return Tree.leaf (← mkEqRefl e)
  | _, _, _ =>
      throwError "Tree mismatch"

abbrev FeasibilityProof := Expr
abbrev FeasibilityProofs := Array FeasibilityProof
abbrev FeasibilityProofsTree := Tree FeasibilityProofs Unit

/-- -/
partial def mkFeasibility :
  GraphAtomDataTree →
  ReducedExprsWithSolutionTree →
  VCondsTree →
  SolEqAtomProofsTree →
  MetaM FeasibilityProofsTree
  | Tree.node atom childAtoms,
    Tree.node _reducedWithSolution childReducedWithSolution,
    Tree.node vcondVars childVCondVars,
    Tree.node _solEqAtom childSolEqAtom => do
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
  | Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _ =>
      return Tree.leaf ()
  | _, _, _, _ =>
      throwError "Tree mismatch"

abbrev OptimalityProof := Expr

abbrev VCondElimProof := Expr
abbrev VCondElimProofs := Array VCondElimProof

abbrev OptimalityAndVCondElimProofs := OptimalityProof × VCondElimProofs
abbrev OptimalityAndVCondElimProofsTree := Tree OptimalityAndVCondElimProofs OptimalityAndVCondElimProofs

-- TODO: What does this actually return?

-- What we call optimality is really the building blocks of
-- the backward map.
-- This is in fact the optimality property but with arguments applied to it.

-- so they look like
--   cone cond => inequality
-- or just
--   inequality (usually when it depends on new vars).
-- vcond elimination

/-- -/
partial def mkOptimalityAndVCondElim :
  GraphAtomDataTree →
  ArgumentsTree →
  ReducedExprsTree →
  NewVarsTree →
  NewConstrVarsTree →
  CurvatureTree →
  BCondsTree →
  MetaM OptimalityAndVCondElimProofsTree
  | Tree.node atom childAtoms,
    Tree.node args childArgs,
    Tree.node _reducedExpr childReducedExpr,
    Tree.node newVars childNewVars,
    Tree.node newConstrVars childNewConstrVars,
    Tree.node curvature childCurvature,
    Tree.node bconds childBConds => do
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

      -- Apply optimality property of atom. TODO: why these and.left/right?
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
partial def mkNewConstrVars :
  NewConstrsTree →
  MetaM NewConstrVarsTree
  | Tree.node newConstr childNewConstr => do
    -- Recursive calls for arguments
    let mut childNewConstrVar := #[]
    for i in [:childNewConstr.size] do
      childNewConstrVar := childNewConstrVar.push <|
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
  (constr : Array (Name × Expr)) : MetaM (Array LocalDecl) := do
withExistingLocalDecls originalVarsDecls.toList do
  let mut decls : Array LocalDecl := #[]
  for i in [:constr.size] do
    decls := decls.push $ LocalDecl.cdecl 0 (← mkFreshFVarId) (Name.mkNum constr[i]!.1 i) constr[i]!.2 Lean.BinderInfo.default LocalDeclKind.default
  return decls

/-- -/
def mkVCondVars (originalConstrVars : Array FVarId) (vcondIdx : Tree (Array (ℕ ⊕ Expr)) Unit) : Tree (Array Expr) Unit :=
  vcondIdx.map (fun iores => iores.map fun iore =>
    match iore with
    | Sum.inl i => mkFVar originalConstrVars[i]!
    | Sum.inr e => e) id

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
def makeConstrForward (oldDomain : Expr) (xs : Array Expr) (originalConstrVars : Array LocalDecl)
  (oldProblem : Expr) (constraints : Array Expr) (isVCond : Array Bool) (constraintsEq : Array Expr)
  (feasibility : OC (Tree (Array Expr) Unit)) : MetaM Expr := do
  -- ∀ {x : D}, Minimization.constraints p x → Minimization.constraints q (f x)

  withLocalDeclD `p oldDomain fun p => do
    let prs := (← Meta.mkProjections oldDomain p).map (·.2.2)

    withLocalDeclD `h (← mkAppM ``Minimization.constraints #[oldProblem, p]) fun h => do
      let (_, cprs) := Meta.composeAndWithProj constraints.toList
      let hProj := (cprs h).toArray

      -- Old constraint proofs.
      let mut oldConstrProofs := #[]
      for i in [:originalConstrVars.size] do
        if not isVCond[i]! then
          oldConstrProofs := oldConstrProofs.push $
            ← mkAppM ``Eq.mpr #[constraintsEq[i]!, mkFVar originalConstrVars[i]!.fvarId]

      -- New constraint proofs.
      let newConstrProofs := feasibility.fold #[] fun acc fs =>
          fs.fold acc Array.append

      let constrForwardBody ← foldAndIntro $ (oldConstrProofs ++ newConstrProofs)
      let constrForwardBody := constrForwardBody.replaceFVars
        ((originalConstrVars).map (mkFVar ·.fvarId)) hProj
      let constrForwardBody ← mkLambdaFVars #[h] constrForwardBody
      let constrForwardBody := constrForwardBody.replaceFVars xs prs.toArray
      let constrForward ← mkLambdaFVars #[p] constrForwardBody
      trace[Meta.debug] "constrForward: {constrForward}"
      trace[Meta.debug] "constrForwardType: {← inferType constrForward}"
      check constrForward
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
      trace[Meta.debug] "constrBackward checked"
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
def mkAtomTree (objCurv : Curvature) (originalVarsDecls : Array LocalDecl) (oc : OC Expr) :
  MetaM (
    OC Bool ×
    OC (Array MessageData) ×
    OC (Tree GraphAtomData Expr) ×
    OC (Tree (Array Expr) Unit) ×
    OC (Tree Curvature Curvature) ×
    OC (Tree (Array Expr) (Array Expr))) := do
withExistingLocalDecls originalVarsDecls.toList do
  let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
  trace[Meta.debug] "mkAtomTree xs: {xs}"
  -- Find atoms.
  let atomsAndArgs ← OC.map2M (fun e c => findAtoms e (xs.map (·.fvarId!)) c) oc
    ⟨objCurv, oc.constr.map (fun _ => Curvature.ConvexSet)⟩
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
  MetaM (OC (Tree (Array ℕ) Unit) × Array Bool × OC (Tree (Array Expr) Unit)) := do
withExistingLocalDecls originalVarsDecls.toList do
  let vcondData ← OC.map2M (findVConditions originalConstrVars oc.constr) atoms args

  -- Extract only indicies
  let vcondIdx : OC (Tree (Array ℕ) Unit) := vcondData.map
    (fun t => t.map (fun iores => iores.foldl (init := #[]) (fun (acc : Array ℕ) iore =>
      match iore with
      | Sum.inl i => acc.push i
      | Sum.inr _ => acc))
      id)

  let isVCond := vcondIdx.fold (oc.constr.map (fun _ => false))
    fun acc vcondIdxTree =>
      vcondIdxTree.fold acc fun acc is =>
        is.foldl (fun acc i => acc.set! i true) acc
  let vcondVars := vcondData.map $ mkVCondVars (originalConstrVars.map LocalDecl.fvarId)
  for i in [:isVCond.size] do
    if failedAtom.constr[i]! ∧ ¬ isVCond[i]! then
      throwError "Failure in constraint {constraints.toArray[i]!.1}: {failedAtomMsgs.constr[i]!}"
  return (vcondIdx, isVCond, vcondVars)

/-- -/
def mkSolEqAtomOC (originalVarsDecls : Array LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr))
  (reducedWithSolution : OC ReducedExprsWithSolutionTree)
  (vcondVars : OC (Tree (Array Expr) Unit)) (originalConstrVars : Array LocalDecl) : MetaM (OC (Tree Expr Expr)) :=
withExistingLocalDecls originalVarsDecls.toList do
  withExistingLocalDecls originalConstrVars.toList do
    let solEqAtom ← OC.map3M mkSolEqAtom atoms reducedWithSolution vcondVars
    trace[Meta.debug] "solEqAtom {solEqAtom}"
    return solEqAtom

/-- -/
def mkFeasibilityOC (originalVarsDecls : Array LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr)) (reducedWithSolution : OC ReducedExprsWithSolutionTree)
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
  (newConstrVarsArray : Array LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr))
  (args : OC (Tree (Array Expr) Unit))
  (reducedExprs : OC (Tree Expr Expr))
  (newVars : OC (Tree (Array LocalDecl) Unit))
  (newConstrVars : OC (Tree (Array LocalDecl) Unit))
  (curvature : OC (Tree Curvature Curvature))
  (bconds : OC (Tree (Array Expr) (Array Expr)))
  (vcondIdx : OC (Tree (Array ℕ) Unit))
  : MetaM (OC (Tree Expr Expr) × Std.HashMap ℕ Expr):=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
      withExistingLocalDecls newConstrVarsArray.toList do
        let optimalityAndVCondElim ← OC.map7M mkOptimalityAndVCondElim atoms args reducedExprs newVars newConstrVars curvature bconds
        let optimality := optimalityAndVCondElim.map (fun oce => oce.map Prod.fst Prod.fst)
        let vcondElim := optimalityAndVCondElim.map (fun oce => oce.map Prod.snd Prod.snd)
        trace[Meta.debug] "optimality {optimality}"
        trace[Meta.debug] "vcondElim {vcondElim}"

        trace[Meta.debug] "vcondIdx {vcondIdx}"
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
  (isVCond : Array Bool)
  (vcondElimMap : Std.HashMap ℕ Expr)
  (solEqAtom : OC (Tree Expr Expr))
  (feasibility : OC (Tree (Array Expr) Unit))
  (reducedExprs : OC (Tree Expr Expr))
  (optimality : OC (Tree Expr Expr))

/-- -/
def mkProcessedAtomTree (objCurv : Curvature) (objFun : Expr) (constraints : List (Lean.Name × Expr)) (originalVarsDecls : Array LocalDecl)
  : MetaM ProcessedAtomTree := do
  let oc ← mkOC objFun constraints originalVarsDecls
  let (failedAtom, failedAtomMsgs, atoms, args, curvature, bconds) ← mkAtomTree objCurv originalVarsDecls oc
  let originalConstrVars ← mkOriginalConstrVars originalVarsDecls constraints.toArray
  let (vcondIdx, isVCond, vcondVars) ← mkVConditions originalVarsDecls oc constraints atoms args failedAtom
    failedAtomMsgs originalConstrVars
  let newVars ← withExistingLocalDecls originalVarsDecls.toList do
    OC.map2MwithCounter mkNewVars atoms args
  let newVarDecls ← mkNewVarDeclList newVars
  let reducedWithSolution ← withExistingLocalDecls originalVarsDecls.toList do
    OC.mapM mkReducedWithSolution atoms
  let forwardImagesNewVars ← withExistingLocalDecls originalVarsDecls.toList do
    mkForwardImagesNewVars reducedWithSolution
  let solEqAtom ← mkSolEqAtomOC originalVarsDecls atoms reducedWithSolution vcondVars originalConstrVars
  let feasibility ← mkFeasibilityOC originalVarsDecls atoms reducedWithSolution vcondVars
    originalConstrVars solEqAtom
  let reducedExprs ← mkReducedExprsOC originalVarsDecls newVarDecls atoms newVars
  let (newConstrs, newConstrVars, newConstrVarsArray)
    ← mkNewConstrsOC originalVarsDecls newVarDecls atoms newVars reducedExprs
  let (optimality, vcondElimMap) ← mkOptimalityAndVCondElimOC originalVarsDecls newVarDecls
    newConstrVarsArray atoms args reducedExprs newVars newConstrVars curvature bconds vcondIdx

  return ProcessedAtomTree.mk
    (originalVarsDecls := originalVarsDecls)
    (originalConstrVars := originalConstrVars)
    (newVarDecls := newVarDecls)
    (newConstrs := newConstrs)
    (newConstrVarsArray := newConstrVarsArray)
    (forwardImagesNewVars := forwardImagesNewVars)
    (constraints := constraints)
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
  let pat ← mkProcessedAtomTree Curvature.Convex objFun constraints originalVarsDecls

  -- Create new goal and reduction.
  let (forwardMap, backwardMap, reduction) ← withExistingLocalDecls pat.originalVarsDecls.toList do
      let xs := pat.originalVarsDecls.map fun decl => mkFVar decl.fvarId

      let forwardMap ← makeForwardMap goalExprs.domain xs pat.forwardImagesNewVars

      let (objFunForward, constrForward) ←
        withExistingLocalDecls pat.originalConstrVars.toList do

          let objFunForward ← makeObjFunForward goalExprs.domain xs pat.originalConstrVars goalExprs.toMinimizationExpr.toExpr
            (pat.constraints.toArray.map Prod.snd) pat.solEqAtom.objFun.val
          let constrForward ← makeConstrForward goalExprs.domain xs pat.originalConstrVars goalExprs.toMinimizationExpr.toExpr
            (pat.constraints.toArray.map Prod.snd) pat.isVCond (pat.solEqAtom.constr.map Tree.val) pat.feasibility

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
        trace[Meta.debug] "res: {res}"

        let res := mkApp res (mkBVar 0) -- Insert new goal here later.
        let res := mkApp6 res
          forwardMap
          (← zetaReduce backwardMap)
          objFunForward
          objFunBackward
          constrForward
          (← zetaReduce constrBackward)
        let res := mkLambda `sol Lean.BinderInfo.default newProblemExpr res

        check res
        trace[Meta.debug] "second check passed"
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
