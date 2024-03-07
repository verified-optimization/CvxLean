import CvxLean.Meta.Util.Expr
import CvxLean.Tactic.Arith.Arith
import CvxLean.Tactic.DCP.DCPTypes
import CvxLean.Tactic.DCP.DCPFindAtoms

namespace CvxLean

open Lean Meta Expr

namespace DCP

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
  let newVarTrees := #[newVars.objFun] ++ newVars.constrs
  let mut newVarDecls := #[]
  for t in newVarTrees do
    newVarDecls := t.fold newVarDecls Array.append
  return newVarDecls.toList


/-- -/
partial def mkCanonExprs : GraphAtomDataTree → NewVarsTree → MetaM (Tree Expr Expr)
  | Tree.node atom childAtoms, Tree.node newVars childNewVars => do
    let mut childCanonExprs := #[]
    for i in [:childAtoms.size] do
      childCanonExprs := childCanonExprs.push $ ← mkCanonExprs childAtoms[i]! childNewVars[i]!
    let canonExpr := atom.impObjFun
    let canonExpr := mkAppNBeta canonExpr (childCanonExprs.map (·.val))
    let canonExpr := mkAppNBeta canonExpr (newVars.map (mkFVar ·.fvarId))
    return Tree.node canonExpr childCanonExprs
  | Tree.leaf e, Tree.leaf () => pure $ Tree.leaf e
  | _, _ => throwError "Tree mismatch"

/-- -/
partial def mkNewConstrs : GraphAtomDataTree → BCondsTree → NewVarsTree → CanonExprsTree → MetaM NewConstrsTree
  | Tree.node atom childAtoms, Tree.node bconds childBConds, Tree.node newVars childNewVars, Tree.node canonExprs childCanonExprs => do
    let mut childNewConstrs := #[]
    for i in [:childAtoms.size] do
      childNewConstrs := childNewConstrs.push <| ← mkNewConstrs childAtoms[i]! childBConds[i]! childNewVars[i]! childCanonExprs[i]!
    let newConstrs := atom.impConstrs
    let newConstrs := newConstrs.map (mkAppNBeta · (childCanonExprs.map Tree.val))
    let newConstrs := newConstrs.map (mkAppNBeta · bconds)
    let newConstrs := newConstrs.map (mkAppNBeta · (newVars.map (mkFVar ·.fvarId)))
    return Tree.node newConstrs childNewConstrs
  | Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _ => pure $ Tree.leaf ()
  | _, _, _, _ => throwError "Tree mismatch"

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
        -- Infer vconditions from constraints.
        vcondData := ←
          withExistingLocalDecls originalConstrVars.toList do
            let (e, _) ← Lean.Elab.Term.TermElabM.run <| Lean.Elab.Term.commitIfNoErrors? <| do
              let tac ← `(by arith)
              let v ← Lean.Elab.Term.elabTerm tac.raw (some vcond)
              Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
              instantiateMVars v

            if let some e' := e then
              return vcondData.push (Sum.inr e')
            else
              throwError
                "Variable condition for {atom.id} not found or inferred: \n {vcond} {constraints}."

    return (Tree.node vcondData childrenVCondData)
  | Tree.leaf _, Tree.leaf _ => pure (Tree.leaf ())
  | _, _ => throwError "Tree mismatch."

/-- Returns the canon expression and an array of forward images of new vars -/
partial def mkCanonWithSolution : GraphAtomDataTree → MetaM CanonExprsWithSolutionTree
  | Tree.node atom childAtoms => do
      let mut childCanonExprs := #[]
      for i in [:childAtoms.size] do
        childCanonExprs := childCanonExprs.push $ ← mkCanonWithSolution childAtoms[i]!
      let sols := (atom.solution.map (mkAppNBeta · (childCanonExprs.1.map (·.val.1)).toArray))
      let canonExpr := atom.impObjFun
      let canonExpr := mkAppNBeta canonExpr (childCanonExprs.1.map (·.val.1)).toArray
      let canonExpr := mkAppNBeta canonExpr sols
      return Tree.node ⟨canonExpr, sols⟩  childCanonExprs
  | Tree.leaf e =>
      return Tree.leaf ⟨e, #[]⟩

/-- Combine all the solutions introduced by every atom expansion. A solution
tells us how to assign new variables from old ones. Here, we collect all such
assignments, which will be used later on to build the forward map between the
original and canon problems. -/
def mkForwardImagesNewVars (canonWithSolution : OC CanonExprsWithSolutionTree) : MetaM Solution := do
  let canonWithSolutionTrees := #[canonWithSolution.objFun] ++ canonWithSolution.constrs
  let mut fm := #[]
  for t in canonWithSolutionTrees do
    fm := t.fold fm (fun acc a => Array.append acc a.solution)
  trace[Meta.debug] "forwardImagesNewVars {fm}"
  return fm

/-- Proofs .-/
partial def mkSolEqAtom :
  GraphAtomDataTree →
  CanonExprsWithSolutionTree →
  VCondsTree →
  MetaM SolEqAtomProofsTree
  | Tree.node atom childAtoms,
    Tree.node canonWithSolution childCanonWithSolution,
    Tree.node vcondVars childVCondVars => do
      -- Recursive calls for arguments.
      let mut childSolEqAtom := #[]
      for i in [:childAtoms.size] do
        childSolEqAtom := childSolEqAtom.push <|
          ← mkSolEqAtom childAtoms[i]! childCanonWithSolution[i]! childVCondVars[i]!
      -- Rewrite arguments in atom expr.
      let mut solEqAtomR ← mkEqRefl atom.expr
      for c in childSolEqAtom do
        solEqAtomR ← mkCongr solEqAtomR c.val
      -- Use solEqAtom of children to rewrite the arguments in the vconditions.
      let mut vconds := #[]
      for i in [:vcondVars.size] do
        let mut vcondEqCanonVCond ← mkEqRefl atom.vconds[i]!.2
        for c in childSolEqAtom do
          vcondEqCanonVCond ← mkCongr vcondEqCanonVCond c.val
        vconds := vconds.push $ ← mkEqMPR vcondEqCanonVCond vcondVars[i]!
      -- Apply solEqAtom property of the atom.
      let solEqAtomL := atom.solEqAtom
      let solEqAtomL := mkAppN solEqAtomL (childCanonWithSolution.map (·.val.1))
      let solEqAtomL := mkAppN solEqAtomL vconds
      let solEqAtom ← mkEqTrans solEqAtomL solEqAtomR
      return Tree.node solEqAtom childSolEqAtom
  | Tree.leaf e, Tree.leaf _, Tree.leaf _ => do
      return Tree.leaf (← mkEqRefl e)
  | _, _, _ =>
      throwError "Tree mismatch"

/-- -/
partial def mkFeasibility :
  GraphAtomDataTree →
  CanonExprsWithSolutionTree →
  BCondsTree →
  VCondsTree →
  SolEqAtomProofsTree →
  MetaM FeasibilityProofsTree
  | Tree.node atom childAtoms,
    Tree.node _canonWithSolution childCanonWithSolution,
    Tree.node bconds childBConds,
    Tree.node vcondVars childVCondVars,
    Tree.node _solEqAtom childSolEqAtom => do
      -- Recursive calls for arguments.
      let mut childFeasibility := #[]
      for i in [:childAtoms.size] do
        let c ← mkFeasibility childAtoms[i]! childCanonWithSolution[i]! childBConds[i]! childVCondVars[i]! childSolEqAtom[i]!
        childFeasibility := childFeasibility.push c
      -- Use solEqAtom of children to rewrite the arguments in the vconditions.
      let mut vconds := #[]
      for i in [:vcondVars.size] do
        let mut vcondEqCanonVCond ← mkEqRefl atom.vconds[i]!.2
        for c in childSolEqAtom do
          vcondEqCanonVCond ← mkCongr vcondEqCanonVCond c.val
        vconds := vconds.push $ ← mkEqMPR vcondEqCanonVCond vcondVars[i]!
      -- Apply feasibility property of the atom.
      let feasibility := atom.feasibility
      let feasibility := feasibility.map (mkAppN · (childCanonWithSolution.map (·.val.1)))
      let feasibility := feasibility.map (mkAppN · bconds)
      let feasibility := feasibility.map (mkAppN · vconds)
      let _ ← feasibility.mapM check
      return Tree.node feasibility childFeasibility
  | Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _  =>
      return Tree.leaf ()
  | _, _, _, _, _ =>
      throwError "Tree mismatch"



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
  CanonExprsTree →
  NewVarsTree →
  NewConstrVarsTree →
  CurvatureTree →
  BCondsTree →
  MetaM OptimalityAndVCondElimProofsTree
  | Tree.node atom childAtoms,
    Tree.node args childArgs,
    Tree.node _canonExpr childCanonExpr,
    Tree.node newVars childNewVars,
    Tree.node newConstrVars childNewConstrVars,
    Tree.node curvature childCurvature,
    Tree.node bconds childBConds => do
      -- Recursive calls for arguments.
      let mut childOptimality := #[]
      let mut childOptimalityFiltered := #[]
      for i in [:childAtoms.size] do
        if atom.argKinds[i]! != ArgKind.Constant ∧ atom.argKinds[i]! != ArgKind.Neither then
          let opt ← mkOptimalityAndVCondElim childAtoms[i]! childArgs[i]! childCanonExpr[i]!
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
      let optimality := mkAppN optimality (childCanonExpr.map Tree.val)
      let optimality := mkAppN optimality bconds
      check optimality
      let optimality := mkAppN optimality (newVars.map (mkFVar ·.fvarId))
      let optimality := mkAppN optimality (newConstrVars.map (mkFVar ·.fvarId))
      let optimality := mkAppN optimality monoArgs
      let optimality := mkAppN optimality (childOptimalityFiltered.map (·.val.1))
      check optimality

      -- Apply vcond elim property of atom.
      let vcondElim := atom.vcondElim
      let vcondElim := vcondElim.map (mkAppN · (childCanonExpr.map Tree.val))
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
def mkAtomTree (objCurv : Curvature) (originalVarsDecls extraDecls : Array LocalDecl) (oc : OC Expr) (extraVars : Array FVarId := #[]) :
  MetaM (
    OC Bool ×
    OC (Array MessageData) ×
    OC (Tree GraphAtomData Expr) ×
    OC (Tree (Array Expr) Unit) ×
    OC (Tree Curvature Curvature) ×
    OC (Tree (Array Expr) (Array Expr))) := do
withExistingLocalDecls originalVarsDecls.toList do
  withExistingLocalDecls extraDecls.toList do
    let decls := (← getLCtx).decls.toList.filterMap fun decl? =>
      if let some decl := decl? then some decl.type else none
    trace[Meta.debug] "decls in mkAtomTree: {decls}"
    let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
    trace[Meta.debug] "mkAtomTree xs: {xs}"
    -- Find atoms.
    let atomsAndArgs ← OC.map2M (fun e c => findAtoms e (xs.map (·.fvarId!) ++ extraVars) c) oc
      ⟨objCurv, oc.constrs.map (fun _ => Curvature.ConvexSet)⟩
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
  let vcondData ← OC.map2M (findVConditions originalConstrVars oc.constrs) atoms args

  -- Extract only indicies
  let vcondIdx : OC (Tree (Array ℕ) Unit) := vcondData.map
    (fun t => t.map (fun iores => iores.foldl (init := #[]) (fun (acc : Array ℕ) iore =>
      match iore with
      | Sum.inl i => acc.push i
      | Sum.inr _ => acc))
      id)

  let isVCond := vcondIdx.fold (oc.constrs.map (fun _ => false))
    fun acc vcondIdxTree =>
      vcondIdxTree.fold acc fun acc is =>
        is.foldl (fun acc i => acc.set! i true) acc
  let vcondVars := vcondData.map $ mkVCondVars (originalConstrVars.map LocalDecl.fvarId)
  for i in [:isVCond.size] do
    if failedAtom.constrs[i]! ∧ ¬ isVCond[i]! then
      throwError "Failure in constraint {constraints.toArray[i]!.1}: {failedAtomMsgs.constrs[i]!}"
  return (vcondIdx, isVCond, vcondVars)

/-- -/
def mkSolEqAtomOC (originalVarsDecls : Array LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr))
  (canonWithSolution : OC CanonExprsWithSolutionTree)
  (vcondVars : OC (Tree (Array Expr) Unit)) (originalConstrVars : Array LocalDecl) : MetaM (OC (Tree Expr Expr)) :=
withExistingLocalDecls originalVarsDecls.toList do
  withExistingLocalDecls originalConstrVars.toList do
    let solEqAtom ← OC.map3M mkSolEqAtom atoms canonWithSolution vcondVars
    trace[Meta.debug] "solEqAtom {solEqAtom}"
    return solEqAtom

/-- -/
def mkFeasibilityOC (originalVarsDecls : Array LocalDecl)
  (atoms : OC GraphAtomDataTree)
  (canonWithSolution : OC CanonExprsWithSolutionTree)
  (bconds : OC BCondsTree)
  (vcondVars : OC VCondsTree)
  (originalConstrVars : Array LocalDecl)
  (solEqAtom : OC SolEqAtomProofsTree) :
  MetaM (OC FeasibilityProofsTree) :=
withExistingLocalDecls originalVarsDecls.toList do
  withExistingLocalDecls originalConstrVars.toList do
    let feasibility ← OC.map5M mkFeasibility atoms canonWithSolution bconds vcondVars solEqAtom
    trace[Meta.debug] "feasibility {feasibility}"
    return feasibility
/-- -/
def mkCanonExprsOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
  (atoms : OC (Tree GraphAtomData Expr)) (newVars : OC (Tree (Array LocalDecl) Unit)) : MetaM (OC (Tree Expr Expr)) :=
withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
        let canonExprs ← OC.map2M mkCanonExprs atoms newVars
        trace[Meta.debug] "canonExprs {canonExprs}"
        return canonExprs

/-- -/
def mkNewConstrsOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
    (bconds : OC BCondsTree)
    (atoms : OC (Tree GraphAtomData Expr))
    (newVars : OC (Tree (Array LocalDecl) Unit))
    (canonExprs : OC (Tree Expr Expr)) :
    MetaM (Array Expr × OC (Tree (Array LocalDecl) Unit) × Array LocalDecl):=
withExistingLocalDecls (originalVarsDecls.toList) do
  withExistingLocalDecls newVarDecls do
    let newConstrs ← OC.map4M mkNewConstrs atoms bconds newVars canonExprs
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
  (canonExprs : OC (Tree Expr Expr))
  (newVars : OC (Tree (Array LocalDecl) Unit))
  (newConstrVars : OC (Tree (Array LocalDecl) Unit))
  (curvature : OC (Tree Curvature Curvature))
  (bconds : OC (Tree (Array Expr) (Array Expr)))
  (vcondIdx : OC (Tree (Array ℕ) Unit))
  : MetaM (OC (Tree Expr Expr) × Std.HashMap ℕ Expr):=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
      withExistingLocalDecls newConstrVarsArray.toList do
        let optimalityAndVCondElim ← OC.map7M mkOptimalityAndVCondElim atoms args canonExprs newVars newConstrVars curvature bconds
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
def mkProcessedAtomTree (objCurv : Curvature) (objFun : Expr)
    (constraints : List (Lean.Name × Expr)) (originalVarsDecls : Array LocalDecl)
    (extraDecls : Array LocalDecl := #[]) (extraVars : Array FVarId := #[]) :
    MetaM ProcessedAtomTree := do
  let oc ← mkOC objFun constraints originalVarsDecls
  let (failedAtom, failedAtomMsgs, atoms, args, curvature, bconds) ← mkAtomTree objCurv originalVarsDecls (extraDecls := extraDecls) (extraVars := extraVars) oc
  let originalConstrVars ← mkOriginalConstrVars originalVarsDecls constraints.toArray
  let (vcondIdx, isVCond, vcondVars) ← mkVConditions originalVarsDecls oc constraints atoms args failedAtom
    failedAtomMsgs originalConstrVars
  let newVars ← withExistingLocalDecls originalVarsDecls.toList do
    OC.map2MwithCounter mkNewVars atoms args
  let newVarDecls ← mkNewVarDeclList newVars
  let canonWithSolution ← withExistingLocalDecls originalVarsDecls.toList do
    OC.mapM mkCanonWithSolution atoms
  let forwardImagesNewVars ← withExistingLocalDecls originalVarsDecls.toList do
    mkForwardImagesNewVars canonWithSolution
  let solEqAtom ← mkSolEqAtomOC originalVarsDecls atoms canonWithSolution vcondVars originalConstrVars
  let feasibility ← mkFeasibilityOC originalVarsDecls atoms canonWithSolution bconds vcondVars
    originalConstrVars solEqAtom
  let canonExprs ← mkCanonExprsOC originalVarsDecls newVarDecls atoms newVars
  let (newConstrs, newConstrVars, newConstrVarsArray)
    ← mkNewConstrsOC originalVarsDecls newVarDecls bconds atoms newVars canonExprs
  let (optimality, vcondElimMap) ← mkOptimalityAndVCondElimOC originalVarsDecls newVarDecls
    newConstrVarsArray atoms args canonExprs newVars newConstrVars curvature bconds vcondIdx

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
    (canonExprs := canonExprs)
    (optimality := optimality)

end DCP

end CvxLean
