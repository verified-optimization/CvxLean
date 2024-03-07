import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Meta
import CvxLean.Tactic.DCP.AtomSyntax
import CvxLean.Tactic.DCP.AtomExt

/-!
# Helpers and elaborators for the `declare_atom` command

This file contains helper functions and elaborators for the `declare_atom` command used in
`CvxLean/Tactic/DCP/AtomCmd.lean`. We define elaborators for every field here that set up the
proof obligations for an atom depending on its signature and implementation.

### TODO

* Make `vconds` available in `impObj`, in the same way that `bconds` are in `elabImpConstrs`? This
  needs to be synchronised with the DCP procedure.
-/

namespace CvxLean

open Lean Expr Meta Elab Term Command

section Helpers

/-- Helper function to add auxiliary atom declarations to the environment. In particular, an atom
declaration involves four proof obligations (which might be split into several sub-proofs). This
function names them and adds them to the environment so that the identifiers can be used to build
proofs later instead of passing around the proof terms.
TODO: This does not respect namespaces. -/
def addAtomDataDecls (id : Name) (atomData : GraphAtomData) : CommandElabM GraphAtomData := do
  if atomData.solEqAtom.hasMVar then
    throwAtomDeclarationError "could not add auxiliary {atomData.solEqAtom} has a metavariable."
  let solEqAtom ← addAtomDataDecl (id.mkStr "solEqAtom") atomData.solEqAtom
  let optimality ← addAtomDataDecl (id.mkStr "optimality") atomData.optimality
  let mut feasibility := #[]
  for i in [:atomData.feasibility.size] do
    feasibility := feasibility.push <|
      ← addAtomDataDecl (id.mkStr (s!"feasibility{i}")) atomData.feasibility[i]!
  let mut vcondElim := #[]
  for i in [:atomData.vcondElim.size] do
    vcondElim := vcondElim.push <|
      ← addAtomDataDecl (id.mkStr (s!"vcondElim{i}")) atomData.vcondElim[i]!
  return { atomData with
    solEqAtom := solEqAtom
    feasibility := feasibility
    vcondElim := vcondElim
    optimality := optimality }
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

/-- Create copy of arguments with non-trivial monotonicities and add them as local declarations.
This is used in `shiftingArgs`, which, in turn, is used to set up the `optimality` and
`vconditionElimination` proof obligations. -/
def withCopyOfMonoXs {α} [Inhabited α] (xs : Array Expr) (argKinds : Array ArgKind)
    (f : Array Expr → Array Expr → Array ArgKind → TermElabM α) : TermElabM α := do
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
    f monoXs ys monoArgKind

/-- The `optimality` and `vconditionElimination` proof obligations statements depend on the
monotonicity of the arguments of the atom. For example, suppose we have a convex atom defined over
a doman `D` with one increasing argument and with one implementation variable `v : E`. Let
`impConstrs` be the implementation constraints of the atom, `impObj` be the implementation objective
and `expr` be the atom's expression. Then, the `optimality` proof obligation will be
`∀ x y : D, ∀ v : E, x ≥ y → impConstrs(x, v) → impObj(x, v) ≥ expr(y)`. This function allows us to
build the "`∀ x y : D, x ≥ y`" part. -/
def shiftingArgs (curv : Curvature) (xs : Array Expr) (argKinds : Array ArgKind)
    (mkConcl : Array Expr → Array Expr → TermElabM Expr) : TermElabM Expr :=
  withCopyOfMonoXs xs argKinds fun monoXs ys monoArgKind => do
    let mut ty := ← mkConcl monoXs ys
    for i' in [:monoXs.size] do
      let i := monoXs.size - 1 - i'
      ty ← match curvatureInArg curv monoArgKind[i]! with
      | Curvature.Concave => mkArrow (← mkLe monoXs[i]! ys[i]!) ty
      | Curvature.Convex => mkArrow (← mkLe ys[i]! monoXs[i]!) ty
      | Curvature.ConvexSet => mkArrow (← mkLe monoXs[i]! ys[i]!) ty
      | _ => throwAtomDeclarationError "invalid curvature"
    return ← mkForallFVars ys ty

/-- Similar to `withCopyOfMonoXs` but only filtering out constant arguments. This is used in affine
atom declarations. -/
def withCopyOfNonConstVars (xs : Array Expr) (argKinds : Array ArgKind)
    (f : Array Expr → Array Expr → TermElabM Expr) : TermElabM Expr := do
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
      -- Use old variable if constant, otherwise use new variable.
      if argKinds[i]! == ArgKind.Constant then
        allYs := allYs.push xs[i]!
      else
        allYs := allYs.push ys[j]!
        j := j + 1
    return ← f ys allYs

end Helpers

section Elaborators

section Signature

/-- Elaborate curvature label in `declare_atom` into a term of type `Curvature`. -/
def elabCurvature (curv : Syntax) : TermElabM Curvature := do
  match curv.getId with
  | `«convex» => return Curvature.Convex
  | `«concave» => return Curvature.Concave
  | `«affine» => return Curvature.Affine
  | `«convex_set» => return Curvature.ConvexSet
  | _ => throwAtomDeclarationError "unknown curvature {curv.getId}."

def elabArgKindsAux : List Syntax → TermElabM (List LocalDecl × List ArgKind)
  | [] => pure ([], [])
  | List.cons stx stxs => do
      match stx with
      | `(arg_with_kind| ($id : $ty) $argkind) => do
          let ty ← Term.elabTerm ty.raw none
          withLocalDeclD id.getId ty fun x => do
            let argkind ←
              match argkind.raw with
                | `(arg_kind| +) => pure ArgKind.Increasing
                | `(arg_kind| -) => pure ArgKind.Decreasing
                | `(arg_kind| ?) => pure ArgKind.Neither
                | `(arg_kind| &) => pure ArgKind.Constant
                | _ => throwAtomDeclarationError "unknown argument kind {argkind}."
            let argDecl ← x.fvarId!.getDecl
            let (argDecls, argKinds) ← elabArgKindsAux stxs
            return (argDecl :: argDecls, argkind :: argKinds)
      | _ => throwUnsupportedSyntax

/-- Given the arguments of an atom declarations (e.g., [`(x : ℝ)+`, `(y : ℝ)-`]), elaborate them
into a list of local declarations and a list of `ArgKind` labels. -/
def elabArgKinds (args : Array Syntax) : TermElabM (Array LocalDecl × Array ArgKind) := do
  let (argDecls, argKinds) ← elabArgKindsAux args.toList
  return (argDecls.toArray, argKinds.toArray)

/-- Elaborate the atom's expression. This depends on the arguments, which we assume have been
elaborated to local declarations. -/
def elabExpr (expr : Syntax) (argDecls : Array LocalDecl) (ty : Option Expr := none) :
    TermElabM (Expr × Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let body ← elabTermAndSynthesizeEnsuringType expr ty
    let bodyTy ← inferType body
    return (← mkLambdaFVars xs body, bodyTy)

/-- Conditions are just expressions (of type `Prop`) defined using the arguments. It is useful to
have them also as a hashmap for variable condition elimination.
TODO: Some duplication here, we essentially return the same data twice. -/
def elabVConditions (argDecls : Array LocalDecl) (vcondStx : Array Syntax) :
    TermElabM (Array (Name × Expr) × Std.HashMap Name Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let mut vcondMap : Std.HashMap Lean.Name Expr := {}
    let mut vconds : Array (Lean.Name × Expr) := #[]
    for stx in vcondStx do
      let vcond ← elabTermAndSynthesizeEnsuringType stx[3] (some <| mkSort levelZero)
      let vcond ← mkLambdaFVars xs vcond
      vcondMap := vcondMap.insert stx[1].getId vcond
      vconds := vconds.push (stx[1].getId, vcond)
    return (vconds, vcondMap)

/-- Background conditions can be elaborated exactly like variable conditions. -/
def elabBConds := elabVConditions

end Signature

section GraphImplementation

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
          trace[CvxLean.debug] "impConstr: {← inferType impConstr}"
          impConstrs := impConstrs.push (stx[1].getId, impConstr)
        return impConstrs

end GraphImplementation

section ProofObligations

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
      | none => throwAtomDeclarationError "Unknown variable: {stx[1].getId}"
      let ty := mkAppNBeta id xs
      solMap := solMap.insert stx[1].getId $ ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] (some ty)
    let sols ← impVarNames.mapM
      fun n => match solMap.find? n with
        | some sol => pure sol
        | none => throwAtomDeclarationError "solution not found {n}"
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
      trace[CvxLean.debug] "ensuring type {ty}"
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
          throwAtomDeclarationError "Feasibility: Expected {impConstrs[i]!.1}, found {(stx[i]!)[1]!}"
        let ty := convertLambdasToLets impConstrs[i]!.2 sols
        let f ← Elab.Term.elabTermAndSynthesizeEnsuringType (stx[i]!)[3]! (some ty)
        let f ← mkLambdaFVars xs $ ← mkLambdaFVars as $ ← mkLambdaFVars cs f
        feas := feas.push f
      return feas

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
            | Curvature.ConvexSet => return ← mkLe impObj body
            | _ => throwAtomDeclarationError "invalid curvature: {curv}"
          trace[CvxLean.debug] "elabOpt ensuring {ty}"
          let opt ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
          trace[CvxLean.debug] "elabOpt opt: {← inferType opt}"
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
              | none => throwAtomDeclarationError "Unknown vcondition: {(stx[i]!)[1]!.getId}"
              let body := mkAppNBeta id xs
              let body := body.replaceFVars monoXs ys
              return body
            let vcondElim ← Elab.Term.elabTermAndSynthesizeEnsuringType (stx[i]!)[3]! (some $ ty)
            let vcondElim ← mkLambdaFVars xs $ ← mkLambdaFVars vs $ ← mkLambdaFVars is vcondElim
            vcondElimMap := vcondElimMap.insert (stx[i]!)[1]!.getId vcondElim
          return ← vconds.mapM
            fun (n, _) => match vcondElimMap.find? n with
              | some vcond => pure vcond
              | none => throwAtomDeclarationError "vcondition not found: {n}"

end ProofObligations

end Elaborators

end CvxLean
