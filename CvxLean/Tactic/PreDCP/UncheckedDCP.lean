import CvxLean.Syntax.OptimizationParam
import CvxLean.Meta.Util.Expr
import CvxLean.Tactic.DCP.DCP

namespace CvxLean

open Lean Meta

namespace UncheckedDCP

partial def mkUncheckedTree (originalVarsDecls : Array LocalDecl) (oc : OC (Name × Expr)) :
  MetaM (OC (String × Tree String String)) := do
  withExistingLocalDecls originalVarsDecls.toList do
    let xs := originalVarsDecls.map fun decl => mkFVar decl.fvarId
    oc.mapM (fun (n, e) => do
      let uncheckedAtomTree ← findUncheckedAtoms e (xs.map (·.fvarId!))
      return (n.toString, uncheckedAtomTree))
where
  findUncheckedAtoms (e : Expr) (vars : Array FVarId) : MetaM (Tree String String) := do
    if e.isRelativelyConstant vars then
      -- NOTE: There are special cases for constants with negation and
      -- division, but what about something like 2 * 3?
      if ← isOptimizationParam e.constName then
        return Tree.node "param" #[Tree.leaf (toString e.constName)]
      let mut e := e
      let mut res := Tree.leaf "unknown"
      let mut hasNeg := false
      if e.getAppFn.constName == `Neg.neg then
        e := e.getArg! 2
        hasNeg := true
      if e.getAppFn.constName == `HDiv.hDiv then
        let a ← Lean.PrettyPrinter.ppExpr <| e.getArg! 4
        let b ← Lean.PrettyPrinter.ppExpr <| e.getArg! 5
        res := Tree.node "div" #[Tree.leaf s!"{a}", Tree.leaf s!"{b}"]
      else
        let ppe ← Lean.PrettyPrinter.ppExpr e
        res := Tree.leaf s!"{ppe}"
      if hasNeg then
        res := Tree.node "neg" #[res]
      return res
    if e.isFVar ∧ vars.contains e.fvarId! then
      let n := (originalVarsDecls.find? (fun decl => decl.fvarId == e.fvarId!)).get!.userName
      return Tree.leaf (toString n)

    -- Special support for less-than.
    if e.getAppFn.constName == `LT.lt then
      let a ← findUncheckedAtoms (e.getArg! 2) vars
      let b ← findUncheckedAtoms (e.getArg! 3) vars
      return Tree.node "lt" #[a, b]

    -- No filter after this, we just take any atoms that are registered.
    let potentialAtoms ← DCP.findRegisteredAtoms e

    -- Just get the first one for now.
    let mut res := Tree.leaf "unknown"
    trace[Meta.debug] s!"potentialAtoms size: {potentialAtoms.size}"
    for (args, atom) in potentialAtoms do
      res ← processUncheckedAtom e vars atom args
      break

    return res

  processUncheckedAtom (e : Expr) (vars : Array FVarId) (atom : GraphAtomData) (args : Array Expr)
  : MetaM (Tree String String) := do
    let mut childTrees := #[]
    for i in [:args.size] do
      let arg := args[i]!
      let childTree ← findUncheckedAtoms arg vars
      childTrees := childTrees.push childTree

    return Tree.node (toString atom.id) childTrees

/-- -/
def uncheckedTreeFromMinimizationExpr (goalExprs : MinimizationExpr) :
  MetaM (OC (String × Tree String String)) := do
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

  let oc ← DCP.mkOCWithNames objFun constraints originalVarsDecls
  let tree ← mkUncheckedTree originalVarsDecls oc
  return tree

end UncheckedDCP

end CvxLean
