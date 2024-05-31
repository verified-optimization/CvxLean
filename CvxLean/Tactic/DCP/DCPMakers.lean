import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Error
import CvxLean.Tactic.Arith.Arith
import CvxLean.Tactic.DCP.DCPTypes
import CvxLean.Tactic.DCP.DCPFindAtoms

/-!
# DCP makers

This is the "processing" step of the DCP procedure. Given a starting problem, we make an atom tree,
and package all the necessary information that is needed to build the equivalence into a
`ProcessedAtomTree` (see `mkProcessedAtomTree`).

See `CvxLean/Tactic/DCP/DCP.lean` for the canonization algorithm that uses the processed atom tree
to build the equivalence.
-/

namespace CvxLean

open Lean Meta Expr

namespace DCP

section MainMakers

/-- Create local declarations for each of the constraints in the original problem. This function is
the only one in this section that does not operate on the canonized problem. -/
def mkOriginalConstrVars (originalVarsDecls : Array LocalDecl) (constr : Array (Name × Expr)) :
    MetaM (Array LocalDecl) := do
  withExistingLocalDecls originalVarsDecls.toList do
    let mut decls : Array LocalDecl := #[]
    for i in [:constr.size] do
      decls := decls.push <| LocalDecl.cdecl 0 (← mkFreshFVarId) (Name.mkNum constr[i]!.1 i)
        constr[i]!.2 Lean.BinderInfo.default LocalDeclKind.default
    return decls

/-- Build the atom tree for the whole problem. Essentially, use `findAtoms` on every component,
setting the expected curvature of the objective function to "convex" and the expected curvature for
each of the constraints to "convex set". -/
def mkAtomTree (objCurv : Curvature) (originalVarsDecls extraDecls : Array LocalDecl) (oc : OC Expr)
    (extraVars : Array FVarId := #[]) :
    MetaM (
      OC Bool × OC (Array MessageData) ×
      OC GraphAtomDataTree × OC ArgumentsTree × OC CurvatureTree × OC BCondsTree) := do
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls extraDecls.toList do
      let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
      -- Find atoms.
      let atomsAndArgs ← OC.map2M (fun e c => findAtoms e (xs.map (·.fvarId!) ++ extraVars) c) oc
        ⟨objCurv, oc.constrs.map (fun _ => Curvature.ConvexSet)⟩
      let failedAtom : OC Bool := atomsAndArgs.map (·.fst)
      let failedAtomMsgs : OC (Array MessageData) := atomsAndArgs.map (·.snd.fst)
      if failedAtom.objFun then
        throwDCPError
          "failed to make atom tree for the objective function ({failedAtomMsgs.objFun})."

      let atoms := atomsAndArgs.map (·.snd.snd.fst)
      let args := atomsAndArgs.map (·.snd.snd.snd.fst)
      let curvature := atomsAndArgs.map (·.snd.snd.snd.snd.fst)
      let bconds := atomsAndArgs.map (·.snd.snd.snd.snd.snd)

      return (failedAtom, failedAtomMsgs, atoms, args, curvature, bconds)

/-- Returns a tree of the new variables added at every node in the atom tree and the total number of
new variables. Freshness is guaranteed by giving each variable a unique name here, using the
counter. -/
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
        newVars := newVars.push <|
          LocalDecl.cdecl 0 (← mkFreshFVarId) (Name.mkNum n i) (mkAppNBeta ty args)
            Lean.BinderInfo.default LocalDeclKind.default
        i := i + 1
      return (Tree.node newVars childNewVars, i)
  | Tree.leaf _, Tree.leaf _ => pure (Tree.leaf (), i)
  | _, _ => throwDCPError "new variables tree mismatch."

/-- Turn `NewVarTree`s (which hold local declarations at the nodes) into one list of local
declarations. -/
def mkNewVarDeclList (newVars : OC NewVarsTree) : MetaM (List LocalDecl) := do
  let newVarTrees := #[newVars.objFun] ++ newVars.constrs
  let mut newVarDecls := #[]
  for t in newVarTrees do
    newVarDecls := t.fold newVarDecls Array.append
  return newVarDecls.toList

/-- Extract the atoms' implementation objectives from the atom tree so that the resulting tree
represents the canonized expressions. -/
partial def mkCanonExprs : GraphAtomDataTree → NewVarsTree → MetaM CanonExprsTree
  | Tree.node atom childAtoms, Tree.node newVars childNewVars => do
      let mut childCanonExprs := #[]
      for i in [:childAtoms.size] do
        childCanonExprs := childCanonExprs.push <| ← mkCanonExprs childAtoms[i]! childNewVars[i]!
      let canonExpr := atom.impObjFun
      let canonExpr := mkAppNBeta canonExpr (childCanonExprs.map (·.val))
      let canonExpr := mkAppNBeta canonExpr (newVars.map (mkFVar ·.fvarId))
      return Tree.node canonExpr childCanonExprs
  | Tree.leaf e, Tree.leaf () => pure <| Tree.leaf e
  | _, _ => throwDCPError "canonized expressions tree mismatch."

/-- Put together all the new constraints added by each of the atoms in the atom tree. -/
partial def mkNewConstrs : GraphAtomDataTree → BCondsTree → NewVarsTree → CanonExprsTree →
    MetaM NewConstrsTree
  | Tree.node atom childAtoms, Tree.node bconds childBConds, Tree.node newVars childNewVars,
    Tree.node _canonExprs childCanonExprs => do
      let mut childNewConstrs := #[]
      for i in [:childAtoms.size] do
        childNewConstrs := childNewConstrs.push <|
          ← mkNewConstrs childAtoms[i]! childBConds[i]! childNewVars[i]! childCanonExprs[i]!
      let newConstrs := atom.impConstrs
      let newConstrs := newConstrs.map (mkAppNBeta · (childCanonExprs.map Tree.val))
      let newConstrs := newConstrs.map (mkAppNBeta · bconds)
      let newConstrs := newConstrs.map (mkAppNBeta · (newVars.map (mkFVar ·.fvarId)))
      return Tree.node newConstrs childNewConstrs
  | Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _ => pure <| Tree.leaf ()
  | _, _, _, _ => throwDCPError "new constraints tree mismatch."

/-- Turn a tree of new constraints into a tree of new constraint *variables*, creating a local
declaration for each new constraint. -/
partial def mkNewConstrVars : NewConstrsTree → MetaM NewConstrVarsTree
  | Tree.node newConstr childNewConstr => do
    -- Recursive calls for arguments.
    let mut childNewConstrVar := #[]
    for i in [:childNewConstr.size] do
      childNewConstrVar := childNewConstrVar.push <| ← mkNewConstrVars childNewConstr[i]!
    -- Create variables for the new constraints.
    let mut newConstrVars : Array LocalDecl := #[]
    for ty in newConstr do
      newConstrVars := newConstrVars.push <|
        LocalDecl.cdecl 0 (← mkFreshFVarId) `h ty Lean.BinderInfo.default LocalDeclKind.default
    return Tree.node newConstrVars childNewConstrVar
  | Tree.leaf _ => pure <| Tree.leaf ()

/-- Same as `mkCanonExprs` but also attach the solutions for each of the atoms unfolded. -/
partial def mkCanonWithSolution : GraphAtomDataTree → MetaM CanonExprsWithSolutionTree
  | Tree.node atom childAtoms => do
      let mut childCanonExprs := #[]
      for i in [:childAtoms.size] do
        childCanonExprs := childCanonExprs.push <| ← mkCanonWithSolution childAtoms[i]!
      let sols := (atom.solution.map (mkAppNBeta · (childCanonExprs.1.map (·.val.1)).toArray))
      let canonExpr := atom.impObjFun
      let canonExpr := mkAppNBeta canonExpr (childCanonExprs.1.map (·.val.1)).toArray
      let canonExpr := mkAppNBeta canonExpr sols
      return Tree.node ⟨canonExpr, sols⟩ childCanonExprs
  | Tree.leaf e =>
      return Tree.leaf ⟨e, #[]⟩

/-- Combine all the solutions introduced by every atom expansion. A solution tells us how to assign
new variables from old ones. Here, we collect all such assignments, which will be used later on to
build the forward map between the original and canonized problems. -/
def mkForwardImagesNewVars (canonWithSolution : OC CanonExprsWithSolutionTree) :
    MetaM Solution := do
  let canonWithSolutionTrees := #[canonWithSolution.objFun] ++ canonWithSolution.constrs
  let mut fm := #[]
  for t in canonWithSolutionTrees do
    fm := t.fold fm (fun acc a => Array.append acc a.solution)
  return fm

/-- Combine all proofs of "solution-equals-atom" into one tree. A little work is needed here so that
the solutions are in term of the optimization variables and not other "new" variables, so we need to
use the solution-equal-atom proofs from the children to adjust the proofs as required. -/
partial def mkSolEqAtom : GraphAtomDataTree → CanonExprsWithSolutionTree → VCondsTree →
    MetaM SolEqAtomProofsTree
  | Tree.node atom childAtoms,
    Tree.node _canonWithSolution childCanonWithSolution,
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
      -- Use `solEqAtom` of children to rewrite the arguments in the `vconditions`.
      let mut vconds := #[]
      for i in [:vcondVars.size] do
        let mut vcondEqCanonVCond ← mkEqRefl atom.vconds[i]!.2
        for c in childSolEqAtom do
          vcondEqCanonVCond ← mkCongr vcondEqCanonVCond c.val
        vconds := vconds.push <| ← mkEqMPR vcondEqCanonVCond vcondVars[i]!
      -- Apply solEqAtom property of the atom.
      let solEqAtomL := atom.solEqAtom
      let solEqAtomL := mkAppN solEqAtomL (childCanonWithSolution.map (·.val.1))
      let solEqAtomL := mkAppN solEqAtomL vconds
      let solEqAtom ← mkEqTrans solEqAtomL solEqAtomR
      return Tree.node solEqAtom childSolEqAtom
  | Tree.leaf e, Tree.leaf _, Tree.leaf _ => do return Tree.leaf (← mkEqRefl e)
  | _, _, _ => throwDCPError "solution-equals-atom tree mismatch."

/-- Combine all feasibility proofs. Again, we need to replace the solutions using solution-equals-
atom so that all the feasibility proofs are with respect to the optimization variables. -/
partial def mkFeasibility : GraphAtomDataTree → CanonExprsWithSolutionTree → BCondsTree →
    VCondsTree → SolEqAtomProofsTree → MetaM FeasibilityProofsTree
  | Tree.node atom childAtoms,
    Tree.node _canonWithSolution childCanonWithSolution,
    Tree.node bconds childBConds,
    Tree.node vcondVars childVCondVars,
    Tree.node _solEqAtom childSolEqAtom => do
        -- Recursive calls for arguments.
        let mut childFeasibility := #[]
        for i in [:childAtoms.size] do
          let c ← mkFeasibility childAtoms[i]! childCanonWithSolution[i]! childBConds[i]!
            childVCondVars[i]! childSolEqAtom[i]!
          childFeasibility := childFeasibility.push c
        -- Use solEqAtom of children to rewrite the arguments in the vconditions.
        let mut vconds := #[]
        for i in [:vcondVars.size] do
          let mut vcondEqCanonVCond ← mkEqRefl atom.vconds[i]!.2
          for c in childSolEqAtom do
            vcondEqCanonVCond ← mkCongr vcondEqCanonVCond c.val
          vconds := vconds.push <| ← mkEqMPR vcondEqCanonVCond vcondVars[i]!
        -- Apply feasibility property of the atom.
        let feasibility := atom.feasibility
        let feasibility := feasibility.map (mkAppN · (childCanonWithSolution.map (·.val.1)))
        let feasibility := feasibility.map (mkAppN · bconds)
        let feasibility := feasibility.map (mkAppN · vconds)
        let _ ← feasibility.mapM check
        return Tree.node feasibility childFeasibility
  | Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _, Tree.leaf _  => return Tree.leaf ()
  | _, _, _, _, _ => throwError "feasibility proofs tree mismatch."

/-- Gather all the optimality and vcondition elimination proofs. Affine atoms in the role of convex
or concave need to be handled separately and their proof of optimality needs to be adjusted. -/
partial def mkOptimalityAndVCondElim : GraphAtomDataTree → ArgumentsTree → CanonExprsTree →
    NewVarsTree → NewConstrVarsTree → CurvatureTree → BCondsTree →
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
        if atom.argKinds[i]! != ArgKind.Constant && atom.argKinds[i]! != ArgKind.Neither then
          let opt ← mkOptimalityAndVCondElim childAtoms[i]! childArgs[i]! childCanonExpr[i]!
              childNewVars[i]! childNewConstrVars[i]! childCurvature[i]! childBConds[i]!
          childOptimality := childOptimality.push opt
          childOptimalityFiltered := childOptimalityFiltered.push opt
        else
          childOptimality := childOptimality.push <| Tree.leaf (mkStrLit s!"dummy {args[i]!}", #[])
      let mut monoArgs := #[]
      for i in [:args.size] do
        if atom.argKinds[i]! != ArgKind.Constant && atom.argKinds[i]! != ArgKind.Neither then
          monoArgs := monoArgs.push args[i]!

      -- Apply optimality property of atom. Recall that the optimality property of affine atoms is
      -- both the property of concave and convex atoms. That is so that here we can use either as
      -- needed.
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
      trace[CvxLean.debug] "Optimality Leaf {e}."
      return Tree.leaf (← mkAppM ``le_refl #[e], #[])
  | _, _, _, _, _, _, _ =>
      throwDCPError "optimality and vcondition elimination proof tree mismatch."

end MainMakers

section VariableConditions

/- These are the functions that handle variable conditions, including inference. -/

/-- Proofs of variable conditions may come from a constraint exactly (in which case we return the
constraint's identifier), or they might be inferred, in which case we return the proof. -/
def mkVCondVars (originalConstrFVars : Array FVarId) (vcondIdx : PreVCondsTree) :
    Tree (Array Expr) Unit :=
  vcondIdx.map (fun iores => iores.map fun iore =>
    match iore with
    | Sum.inl i => mkFVar originalConstrFVars[i]!
    | Sum.inr e => e) id

/-- Returns index of constraint if vcondition corresponds exactly to a constraint (this is needed
for condition elimination). If not, it tries to deduce the condition from other constraints and
returns an expression. -/
partial def findVConditions (originalConstrVars : Array LocalDecl) (constraints : Array Expr) :
    GraphAtomDataTree → ArgumentsTree → MetaM PreVCondsTree
  | Tree.node atom childAtoms, Tree.node args childArgs => do
      let mut childrenVCondData := #[]
      for i in [:childAtoms.size] do
        let childVCondData ←
          findVConditions originalConstrVars constraints childAtoms[i]! childArgs[i]!
        childrenVCondData := childrenVCondData.push childVCondData
      let mut vcondData := #[]
      for (_, vcond) in atom.vconds do
        let vcond := mkAppNBeta vcond args

        -- First, try to see if it matches exactly with any of the constraints.
        match ← constraints.findIdxM? (isDefEq vcond) with
        | some i => do vcondData := vcondData.push (Sum.inl i)
        | none =>
          -- If not, try to infer vconditions from constraints.
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
                throwDCPError "variable condition for {atom.id} not found or inferred.\n{vcond}\n{constraints}."

      return (Tree.node vcondData childrenVCondData)
  | Tree.leaf _, Tree.leaf _ => pure (Tree.leaf ())
  | _, _ => throwDCPError "variable conditions tree mismatch."

/-- Identify vconditions and check that all failed constraints can be used as vconditions. This also
separates the vconditions that need to be eliminated by putting all their indices together. -/
def mkVConditions (originalVarsDecls : Array LocalDecl) (oc : OC Expr)
    (constraints : List (Name × Expr)) (atoms : OC GraphAtomDataTree) (args : OC ArgumentsTree)
    (failedAtom : OC Bool) (failedAtomMsgs : OC (Array MessageData))
    (originalConstrVars : Array LocalDecl) :
    MetaM (OC VCondsIdxsTree × Array Bool × OC VCondsTree) := do
  withExistingLocalDecls originalVarsDecls.toList do
    let vcondData ← OC.map2M (findVConditions originalConstrVars oc.constrs) atoms args

    -- Extract only indicies
    let vcondIdx : OC VCondsIdxsTree := vcondData.map
      (fun t => t.map (fun iores => iores.foldl (init := #[]) (fun (acc : Array ℕ) iore =>
        match iore with
          | Sum.inl i => acc.push i
          | Sum.inr _ => acc))
        id)

    let isVCond := vcondIdx.fold (oc.constrs.map (fun _ => false))
      fun acc vcondIdxTree =>
        vcondIdxTree.fold acc fun acc is =>
          is.foldl (fun acc i => acc.set! i true) acc
    let vcondVars := vcondData.map <| mkVCondVars (originalConstrVars.map LocalDecl.fvarId)
    for i in [:isVCond.size] do
      if failedAtom.constrs[i]! && !isVCond[i]! then
        throwDCPError
          "failure in constraint {constraints.toArray[i]!.1} ({failedAtomMsgs.constrs[i]!})."
    return (vcondIdx, isVCond, vcondVars)

end VariableConditions

section OC

/- Lift all the basic makers to operate on `OC`s. -/

/-- Extract objective and constraints in terms of the optimization variables. -/
def mkOC (objFun : Expr) (constraints : List (Name × Expr)) (originalVarsDecls : Array LocalDecl) :
    MetaM (OC Expr) := do
  withExistingLocalDecls originalVarsDecls.toList do
    return OC.mk objFun (constraints.toArray.map (fun (c : Name × Expr) => c.2))

/-- Same as `mkOC` but keeping constraint tags. The objective function is tagged with anonymous. -/
def mkOCWithNames (objFun : Expr) (constraints : List (Name × Expr))
    (originalVarsDecls : Array LocalDecl) : MetaM (OC (Name × Expr)) := do
  withExistingLocalDecls originalVarsDecls.toList do
    let oc := OC.mk (`_, objFun) constraints.toArray
    return oc

/-- Lioft `mkSolEqAtom` to `OC`. -/
def mkSolEqAtomOC (originalVarsDecls : Array LocalDecl) (atoms : OC GraphAtomDataTree)
    (canonWithSolution : OC CanonExprsWithSolutionTree) (vcondVars : OC VCondsTree)
    (originalConstrVars : Array LocalDecl) : MetaM (OC SolEqAtomProofsTree) :=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls originalConstrVars.toList do
      let solEqAtom ← OC.map3M mkSolEqAtom atoms canonWithSolution vcondVars
      trace[CvxLean.debug] "`solEqAtom`: {solEqAtom}."
      return solEqAtom

/-- Lift `mkFeasibility` to `OC`. -/
def mkFeasibilityOC (originalVarsDecls : Array LocalDecl) (atoms : OC GraphAtomDataTree)
    (canonWithSolution : OC CanonExprsWithSolutionTree) (bconds : OC BCondsTree)
    (vcondVars : OC VCondsTree) (originalConstrVars : Array LocalDecl)
    (solEqAtom : OC SolEqAtomProofsTree) : MetaM (OC FeasibilityProofsTree) :=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls originalConstrVars.toList do
      let feasibility ← OC.map5M mkFeasibility atoms canonWithSolution bconds vcondVars solEqAtom
      trace[CvxLean.debug] "`feasibility`: {feasibility}."
      return feasibility

/-- Lift `mkCanonExprs` to `OC`. -/
def mkCanonExprsOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
    (atoms : OC GraphAtomDataTree) (newVars : OC NewVarsTree) : MetaM (OC CanonExprsTree) :=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
      let canonExprs ← OC.map2M mkCanonExprs atoms newVars
      trace[CvxLean.debug] "`canonExprs`: {canonExprs}."
      return canonExprs

/-- Lift `mkNewConstrs` and `mkNewConstrVars` to `OC`. Also returns an array containing all the new
constraints as expressions, and an array containing pointers to all their local declarations. -/
def mkNewConstrsOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
    (bconds : OC BCondsTree) (atoms : OC GraphAtomDataTree) (newVars : OC NewVarsTree)
    (canonExprs : OC CanonExprsTree) :
    MetaM (Array Expr × OC NewConstrVarsTree × Array LocalDecl) :=
  withExistingLocalDecls (originalVarsDecls.toList) do
    withExistingLocalDecls newVarDecls do
      let newConstrs ← OC.map4M mkNewConstrs atoms bconds newVars canonExprs
      trace[CvxLean.debug] "`newConstrs` {newConstrs}."
      let newConstrVars ← OC.mapM mkNewConstrVars newConstrs
      trace[CvxLean.debug] "`newConstrsVars`: {newConstrs}."
      let newConstrs : Array Expr := newConstrs.fold #[] fun acc cs =>
        cs.fold acc Array.append
      let newConstrVarsArray : Array LocalDecl := newConstrVars.fold #[] fun acc cs =>
        cs.fold acc Array.append
      return (newConstrs, newConstrVars, newConstrVarsArray)

/-- Lift `optimalityAndVCondElim` to OC and split it into the optimality proofs and the vcondition
elimination map. -/
def mkOptimalityAndVCondElimOC (originalVarsDecls : Array LocalDecl) (newVarDecls : List LocalDecl)
    (newConstrVarsArray : Array LocalDecl) (atoms : OC GraphAtomDataTree) (args : OC ArgumentsTree)
    (canonExprs : OC CanonExprsTree) (newVars : OC NewVarsTree)
    (newConstrVars : OC NewConstrVarsTree) (curvature : OC CurvatureTree) (bconds : OC BCondsTree)
    (vcondIdx : OC VCondsIdxsTree) : MetaM (OC OptimalityProofsTree × VCondElimMap):=
  withExistingLocalDecls originalVarsDecls.toList do
    withExistingLocalDecls newVarDecls do
      withExistingLocalDecls newConstrVarsArray.toList do
        let optimalityAndVCondElim ← OC.map7M mkOptimalityAndVCondElim atoms args canonExprs newVars
          newConstrVars curvature bconds
        let optimality := optimalityAndVCondElim.map (fun oce => oce.map Prod.fst Prod.fst)
        let vcondElim := optimalityAndVCondElim.map (fun oce => oce.map Prod.snd Prod.snd)
        trace[CvxLean.debug] "`optimality`: {optimality}."
        trace[CvxLean.debug] "`vcondElim`: {vcondElim}."
        trace[CvxLean.debug] "`vcondIdx`: {vcondIdx}."
        let vcondElimWithIdx ← OC.map2M (fun a b => Tree.zip a b) vcondIdx vcondElim
        let vcondElimMap := vcondElimWithIdx.fold {}
          fun (map : VCondElimMap) ci =>
            ci.fold map fun (map : VCondElimMap) ci => Id.run do
              let mut res := map
              for i in [:ci.1.size] do
                res := res.insert ci.1[i]! ci.2[i]!
              return res
        return (optimality, vcondElimMap)

end OC

/-- Combine everything into a processed atom tree, starting from the original optimization
problem. First, make the atom tree. Gather all the local declarations (original variables, original
constraints, new variables, new constraints). Get all the forward images (from the solutions of the
atoms), and the canonized expressions for every component. As expected, it also includes all the
necessary proofs, as trees. -/
def mkProcessedAtomTree (objCurv : Curvature) (objFun : Expr) (constraints : List (Name × Expr))
    (originalVarsDecls : Array LocalDecl) (extraDecls : Array LocalDecl := #[])
    (extraVars : Array FVarId := #[]) : MetaM ProcessedAtomTree := do
  let oc ← mkOC objFun constraints originalVarsDecls
  let (failedAtom, failedAtomMsgs, atoms, args, curvature, bconds) ← mkAtomTree objCurv
    originalVarsDecls (extraDecls := extraDecls) (extraVars := extraVars) oc
  let originalConstrVars ← mkOriginalConstrVars originalVarsDecls constraints.toArray
  let (vcondIdx, isVCond, vcondVars) ← mkVConditions originalVarsDecls oc constraints atoms args
    failedAtom failedAtomMsgs originalConstrVars
  let newVars ← withExistingLocalDecls originalVarsDecls.toList do
    OC.map2MwithCounter mkNewVars atoms args
  let newVarDecls ← mkNewVarDeclList newVars
  let canonWithSolution ← withExistingLocalDecls originalVarsDecls.toList do
    OC.mapM mkCanonWithSolution atoms
  let forwardImagesNewVars ← withExistingLocalDecls originalVarsDecls.toList do
    mkForwardImagesNewVars canonWithSolution
  let solEqAtom ← mkSolEqAtomOC originalVarsDecls atoms canonWithSolution vcondVars
    originalConstrVars
  let feasibility ← mkFeasibilityOC originalVarsDecls atoms canonWithSolution bconds vcondVars
    originalConstrVars solEqAtom
  let canonExprs ← mkCanonExprsOC originalVarsDecls newVarDecls atoms newVars
  let (newConstrs, newConstrVars, newConstrVarsArray) ←
    mkNewConstrsOC originalVarsDecls newVarDecls bconds atoms newVars canonExprs
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
