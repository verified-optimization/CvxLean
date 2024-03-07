import CvxLean.Meta.Util.Expr
import CvxLean.Tactic.Arith.Arith
import CvxLean.Tactic.DCP.AtomExt
import CvxLean.Tactic.DCP.DCPTypes

/-!
# Finding DCP atom trees

This file defines the procedure to turn an expression into a tree of atoms. This is the first step
of the canonization algorithm. At this point, only background conditions and curvatures are checked.

This is then applied to every component in `mkAtomTree` in `CvxLean/Tactic/DCP/DCPMakers.lean` to
make a full atom tree for the problem.
-/

namespace CvxLean

open Lean Meta Expr

namespace DCP

/-- Return list of all registered atoms that match with a given expression. For every registered
atom, it returns:
* The list of arguments as Lean expressions for further matching.
* The atom entry, of type `GraphAtomData`.

Recall that the atom library is stored using a discrimination tree.

There might be multiple atoms that match an expression. This function returns all matches. -/
def findRegisteredAtoms (e : Expr) : MetaM (Array (Arguments × GraphAtomData)) := do
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

/-- Data type used to indicate whether an atom could be successfully processed. It is used by
`processAtom`. A successful match includes 4 trees:
* A tree of atom data (see `GraphAtomData`).
* A tree of arguments for every node.
* A tree of curvatures.
* A tree of background conditions. -/
inductive FindAtomResult
  | Success (res : AtomDataTrees)
  | Error (msgs : Array MessageData)

/-- Given an expression `e`, optimization variables `vars` and the expected curvature `curvature`,
this function attempts to recursively match `e` with atoms for the library.

It outputs all the necessary information as explained in `FindAtomResult`. The boolean in the output
indicates whether a match from the library was used. -/
partial def findAtoms (e : Expr) (vars : Array FVarId) (curvature : Curvature) :
    MetaM (Bool × Array MessageData × AtomDataTrees) := do
  let e := eta e

  -- Variable case.
  if e.isFVar ∧ vars.contains e.fvarId! then
    return (false, #[], Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])

  -- Constant case.
  let isConstantExpr := e.isRelativelyConstant vars || curvature == Curvature.Constant
  let isPropExpr := (← inferType e).isProp
  if isConstantExpr && !isPropExpr then
    return (false, #[], Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])

  -- Operator case.
  let potentialAtoms ← findRegisteredAtoms e
  let mut failedAtoms : Array MessageData := #[]
  if potentialAtoms.size == 0 then
    failedAtoms := failedAtoms.push m!"No atom found for {e}"
  -- Go through all the matches, and stop on the first successful one.
  for (args, atom) in potentialAtoms do
    match ← processAtom e vars curvature atom args with
    | FindAtomResult.Success (atoms, args, curvatures, bconds) =>
        trace[Meta.debug] "Success {e} : {atom}"
        return (false, failedAtoms, atoms, args, curvatures, bconds)
    | FindAtomResult.Error msg =>
        failedAtoms := failedAtoms ++ msg
  return (true, failedAtoms, Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf #[])
where
  /-- This functon takes data from the atom library and succeeds if it can use it to fu-/
  processAtom (e : Expr) (vars : Array FVarId) (curvature : Curvature) (atom : GraphAtomData)
      (args : Array Expr) : MetaM FindAtomResult := do
    trace[CvxLean.debug] "Processing atom {atom.expr} for expression {e}, curvature {curvature}"
    if atom.curvature != Curvature.Affine ∧ curvature != atom.curvature then
      return FindAtomResult.Error
        #[m!"Trying atom {atom.expr} for expression {e}: " ++
          m!"Expected {curvature}, but atom is {atom.curvature}"]
    let mut bconds := #[]
    for (_, bcondType) in atom.bconds do
      let bcondType := mkAppNBeta bcondType args
      let fvarId? ← (← getLCtx).decls.findSomeM? fun decl => match decl with
        | none => pure none
        | some decl => do
          if ← isDefEq decl.type bcondType then return some decl.fvarId else return none
      match fvarId? with
      | some fvarId =>
        bconds := bconds.push (mkFVar fvarId)
      | none =>
        -- Try to prove simple bconditions by `arith`.
        let (e, _) ← Lean.Elab.Term.TermElabM.run <| Lean.Elab.Term.commitIfNoErrors? <| do
          let v ← Lean.Elab.Term.elabTerm (← `(by arith)).raw (some bcondType)
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let v ← instantiateMVars v
          return v
        if let some e' := e then
          bconds := bconds.push e'
        else
          let declsTypes := (← getLCtx).decls.toList.filterMap (Option.map LocalDecl.type)
          return FindAtomResult.Error
            #[m!"Trying atom {atom.expr} for expression {e}: " ++
              m!"Background Condition {bcondType} not found. (Local context: {declsTypes})"]

    let mut childTrees := #[]
    let mut childArgsTrees := #[]
    let mut childCurvatures := #[]
    let mut childBConds := #[]
    for i in [:args.size] do
      let arg := args[i]!
      if atom.argKinds[i]! == ArgKind.Constant ∧ not (arg.isRelativelyConstant vars) then
        return FindAtomResult.Error
          #[m!"Trying atom {atom.expr} for expression {e}: " ++
            m!"Expected constant argument, but found: {arg}"]
      -- Apply curvature rule to find expected curvature of the argument.
      let c := curvatureInArg curvature atom.argKinds[i]!
      trace[CvxLean.debug] "Trying to find atoms for {arg} with curvature {c}."
      -- Recursion happends here, where we try to find atoms
      let (childFailed, childFailedAtoms, childTree, childArgsTree, childCurvature, childBCond) ←
        findAtoms arg vars c
      if childFailed then
        return FindAtomResult.Error childFailedAtoms
      childTrees := childTrees.push childTree
      childArgsTrees := childArgsTrees.push childArgsTree
      childCurvatures := childCurvatures.push childCurvature
      childBConds := childBConds.push childBCond
    if curvature == Curvature.Affine then
      -- For affine branches, we simply return the expression.
      return FindAtomResult.Success
        (Tree.leaf e, Tree.leaf (), Tree.leaf curvature, Tree.leaf bconds)
    else
      return FindAtomResult.Success (
        Tree.node atom childTrees,
        Tree.node args childArgsTrees,
        Tree.node curvature childCurvatures,
        Tree.node bconds childBConds)

end DCP

end CvxLean
