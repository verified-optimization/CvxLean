import CvxLean.Lib.Math.Data.Real
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
  addAtomDataDecl (name : Name) (expr : Expr) : CommandElabM Expr := do
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
  let mut argDeclInfo : Array (Name × (Array Expr → TermElabM Expr)) := #[]
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
  let mut argDeclInfo : Array (Name × (Array Expr → TermElabM Expr)) := #[]
  for i in [:xs.size] do
    if argKinds[i]! != ArgKind.Constant then
      let ty := ← inferType xs[i]!
      let name := Name.mkSimple ((toString (← FVarId.getDecl xs[i]!.fvarId!).userName) ++ "'")
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

/-- Apply a function to non-constant arguments. Used by affine atom elaborators. -/
def mapNonConstant (xs : Array Expr) (argKinds : Array ArgKind) (f : Expr → TermElabM Expr) :
    TermElabM (Array Expr) :=
  (Array.zip xs argKinds).mapM fun (x, kind) => do
    if kind == ArgKind.Constant then return x else return ← f x

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
TODO: Some duplication here, we essentially return the same data twice. There is a similar issue
with other functions below. -/
def elabVConditions (argDecls : Array LocalDecl) (vcondStx : Array Syntax) :
    TermElabM (Array (Name × Expr) × Std.HashMap Name Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let mut vcondMap : Std.HashMap Name Expr := {}
    let mut vconds : Array (Name × Expr) := #[]
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

/-- The implementation variables used in the graph implementation of ana tom are given as
identifiers with a type such as `(t : ℝ)`. Here, we get the names and types of all implementation
variables. Their types might depend on the arguments, mainly with vectors or arrays where the type
is, say, `Fin n → ℝ`, and `n` is an atom argument. -/
def elabImpVars (argDecls : Array LocalDecl) (impVarsStx : Array Syntax) :
    TermElabM (Array (Name × Expr) × Std.HashMap Name Expr) := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    let mut impVarMap : Std.HashMap Name Expr := {}
    let mut impVars : Array (Name × Expr) := #[]
    for stx in impVarsStx do
      let impVarTy ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] none
      let impVarTy ← mkLambdaFVars xs <| impVarTy
      impVars := impVars.push (stx[1].getId, impVarTy)
      impVarMap := impVarMap.insert stx[1].getId impVarTy
    return (impVars, impVarMap)

/-- The implementation objective is an expression that might depend on the atom arguments and the
implementation variables.
TODO: Add background conditions. -/
def elabImpObj (argDecls : Array LocalDecl) (impVars : Array (Name × Expr))
    (impObjStx : Syntax) (bodyTy : Expr) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    -- `vs` are the implementation variables.
    withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
      let impObj ← Elab.Term.elabTermAndSynthesizeEnsuringType impObjStx (some bodyTy)
      return ← mkLambdaFVars (xs ++ vs) impObj

/-- The implementation constraints are expressions (of type `Prop`) that might depend on the atom
arguments and the implementation variables. Theyc an also use background conditions. -/
def elabImpConstrs (argDecls : Array LocalDecl) (impVars : Array (Name × Expr))
    (bconds : Array (Name × Expr)) (impConstrStx : Array Syntax) :
    TermElabM (Array (Name × Expr)) := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
    -- `as` are the background conditions.
    withLocalDeclsDNondep bconds fun as => do
      -- `vs` are the implementation variables.
      withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
        let mut impConstrs : Array (Name × Expr) := #[]
        for stx in impConstrStx do
          let impConstr ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] (mkSort levelZero)
          let impConstr ← mkLambdaFVars (xs ++ as ++ vs) impConstr
          trace[CvxLean.debug] "`elabImpConstrs` constraint type {← inferType impConstr}."
          impConstrs := impConstrs.push (stx[1].getId, impConstr)
        return impConstrs

end GraphImplementation

section ProofObligations

/-- For every implementation variable, they user must provide a solution as an expression using
the atom's arguments. These expressions are crucial to build the forward map in the equivalence
relation. -/
def elabSols (argDecls : Array LocalDecl) (impVars : Array (Name × Expr))
    (impVarMap : Std.HashMap Name Expr) (solStx : Array Syntax) : TermElabM (Array Expr) := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    let impVarNames := impVars.map (·.fst)
    let mut solMap : Std.HashMap Name Expr := {}
    for stx in solStx do
      let id ← match impVarMap.find? stx[1].getId with
        | some id => pure id
        | none => throwAtomDeclarationError "unknown variable in solution {stx[1].getId}."
      let ty := mkAppNBeta id xs
      solMap := solMap.insert stx[1].getId <|
        ← Elab.Term.elabTermAndSynthesizeEnsuringType stx[3] (some ty)
    let sols ← impVarNames.mapM
      fun n => match solMap.find? n with
        | some sol => pure sol
        | none => throwAtomDeclarationError "solution not found for {n}."
    let sols ← sols.mapM (do return ← mkLambdaFVars xs ·)
    return sols

/-- Given the implementation objecitve and the user-defined solutions, the first proof obligation
is to show that instantiating the implementation variables in the implementaiton objective with the
solution expressions needs to be **equal** to the atom's expression. This is used later on to prove
the needed properties of the forward map. -/
def elabSolEqAtom (argDecls : Array LocalDecl) (vconds : Array (Name × Expr))
    (impObj : Expr) (sols : Array Expr)
    (expr : Expr) (stx : Syntax) : TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    let vconds := vconds.map fun (n,c) => (n, mkAppNBeta c xs)
    withLocalDeclsDNondep vconds fun cs => do
      let body := mkAppNBeta expr xs
      let impObj := mkAppNBeta impObj xs
      let sols := sols.map (mkAppNBeta · xs)
      let impObj' := convertLambdasToLets impObj sols
      let ty ← mkEq impObj' body
      trace[CvxLean.debug] "`elabSolEqAtom` ensuring type {ty}."
      let solEqAtom ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
      mkLambdaFVars (xs ++ cs) solEqAtom

/-- Here, we set up the second proof obligation, or rather list of proof obligations. For every
implmentation constraints, we must show that the solutions satisfy them. This function sets up
the proof goal for each constraint. This is used later on to prove the needed properties of the
forward map. -/
def elabFeas (argDecls : Array LocalDecl) (vconds bconds : Array (Name × Expr))
    (impConstrs : Array (Name × Expr)) (sols : Array Expr) (stx : Array Syntax) :
    TermElabM (Array Expr) := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    let bconds := bconds.map fun (n, c) => (n, mkAppNBeta c xs)
    -- `as` are the background conditions.
    withLocalDeclsDNondep bconds fun as => do
      let vconds := vconds.map fun (n, c) => (n, mkAppNBeta c xs)
      -- `cs` are the variable conditions.
      withLocalDeclsDNondep vconds fun cs => do
      let impConstrs := impConstrs.map fun (n, c) => (n, mkAppNBeta c xs)
      let impConstrs := impConstrs.map fun (n, c) => (n, mkAppNBeta c as)
      let sols := sols.map (mkAppNBeta · xs)
      let mut feas := #[]
      for i in [:impConstrs.size] do
        if (stx[i]!)[1]!.getId != impConstrs[i]!.1 then
          throwAtomDeclarationError
            "expected feasibility {impConstrs[i]!.1}, found {(stx[i]!)[1]!}."
        let ty := convertLambdasToLets impConstrs[i]!.2 sols
        let f ← Elab.Term.elabTermAndSynthesizeEnsuringType (stx[i]!)[3]! (some ty)
        let f ← mkLambdaFVars (xs ++ as ++ cs) f
        feas := feas.push f
      return feas

/-- This proof obligation has to do with how the implementation objective bounds the atom's
expression in the appropriate monotone context. It depends on the curvature of the atom. It has the
following shape. Let `x₁, ..., xₙ` and `y₁, ..., yₙ` be variables in the atom's domain (we only need
to consider the components of the domain where the atom's function has non-trivial monotonicity
(increasing or decreasing)). Let `v₁, ..., vₘ` be the implementation variables. We need to show:
```
h₁ : y₁ ~ x₁
...
hₙ : yₙ ~ xₙ
h : impConstrs(x₁, ..., xₙ, v₁, ..., vₘ)
⊢ impObj(x₁, ..., xₙ, v₁, ..., vₘ) ~ expr(y₁, ..., yₙ)
```
Each `~` is replaced by the appropriate relation depending on the atom's signature.
This is used later on to prove the required properties of the backward map. -/
def elabOpt (curv : Curvature) (argDecls : Array LocalDecl) (expr : Expr)
    (bconds : Array (Name × Expr)) (impVars : Array (Name × Expr)) (impObj : Expr)
    (impConstrs : Array (Name × Expr)) (argKinds : Array ArgKind) (stx : Syntax) :
    TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    -- `xs` are the arguments of the atom.
    let xs := argDecls.map (mkFVar ·.fvarId)
    let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
    -- `as` are the background conditions.
    withLocalDeclsDNondep bconds fun as => do
      -- `vs` are the implementation variables.
      withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c xs)
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c as)
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c vs)
        -- `is` are the implementation constraints.
        withLocalDeclsDNondep impConstrs fun is => do
          let impObj := mkAppNBeta (mkAppNBeta impObj xs) vs
          let ty ← shiftingArgs curv xs argKinds fun monoXs ys =>
            let body := mkAppNBeta expr xs
            let body := body.replaceFVars monoXs ys
            match curv with
              | Curvature.Concave => return ← mkLe impObj body
              | Curvature.Convex => return ← mkLe body impObj
              | Curvature.ConvexSet => return ← mkLe impObj body
              | _ => throwAtomDeclarationError
                  "invalid curvature {curv} found when setting up optimality proof obligation."
          trace[CvxLean.debug] "`elabOpt` ensuring {ty}."
          let opt ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
          trace[CvxLean.debug] "`elabOpt` proof term type {← inferType opt}."
          mkLambdaFVars (xs ++ as ++ vs ++ is) opt

/-- For every variable condition, we must show that it can be proved from the implementation
constraints. This function sets up such goals. This is used later on to prove the required
properties of the backward map. -/
def elabVCondElim (curv : Curvature) (argDecls : Array LocalDecl)
    (bconds vconds : Array (Name × Expr)) (vcondMap : Std.HashMap Name Expr)
    (impVars : Array (Name × Expr)) (impConstrs : Array (Name × Expr)) (argKinds : Array ArgKind)
    (stx : Array Syntax) : TermElabM (Array Expr) := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c xs)
    let bconds := bconds.map fun (n,c) => (n, mkAppNBeta c xs)
    -- `as` are the background conditions.
    withLocalDeclsDNondep bconds fun as => do
      let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c as)
      -- `vs` are the implementation variables.
      withLocalDeclsDNondep (impVars.map fun iv => (iv.1, mkAppNBeta iv.2 xs)) fun vs => do
        let impConstrs := impConstrs.map fun (n,c) => (n, mkAppNBeta c vs)
        -- `is` are the implementation constraints.
        withLocalDeclsDNondep impConstrs fun is => do
          let mut vcondElimMap : Std.HashMap Name Expr := {}
          for i in [:stx.size] do
            let ty ← shiftingArgs curv xs argKinds fun monoXs ys => do
              let id ← match vcondMap.find? (stx[i]!)[1]!.getId with
                | some id => pure id
                | none =>
                    throwAtomDeclarationError "unknown variable condition {(stx[i]!)[1]!.getId}."
              let body := mkAppNBeta id xs
              let body := body.replaceFVars monoXs ys
              return body
            let vcondElim ← Elab.Term.elabTermAndSynthesizeEnsuringType (stx[i]!)[3]! (some <| ty)
            let vcondElim ← mkLambdaFVars (xs ++ vs ++ is) vcondElim
            vcondElimMap := vcondElimMap.insert (stx[i]!)[1]!.getId vcondElim
          return ← vconds.mapM
            fun (n, _) => match vcondElimMap.find? n with
              | some vcond => pure vcond
              | none => throwAtomDeclarationError "variable condition {n} not found."

end ProofObligations

section AffineAtoms

/-- Set up proof of homogeneity. Sanity check for affine atoms. -/
def elabHom (argDecls : Array LocalDecl) (expr : Expr) (argKinds : Array ArgKind) (stx : Syntax) :
    TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    withLocalDeclD `κ (mkConst ``Real) fun κ => do
      let xs := argDecls.map (mkFVar ·.fvarId)
      let zero := mkAppNBeta expr <| ← mapNonConstant xs argKinds
        fun x => do return ← mkNumeral (← inferType x) 0
      let lhs ← mkAdd (← mkAppM ``HSMul.hSMul #[κ, mkAppNBeta expr xs]) zero
      let rhs ← mkAdd
        (mkAppNBeta expr <| ← mapNonConstant xs argKinds fun x => mkAppM ``HSMul.hSMul #[κ, x])
        (← mkAppM ``HSMul.hSMul #[κ, zero])
      let ty ← mkEq lhs rhs
      let hom ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
      return ← mkLambdaFVars xs <| ← mkLambdaFVars #[κ] hom

/-- Set up proof of additivity. Sanity check for affine atoms. -/
def elabAdd (argDecls : Array LocalDecl) (expr : Expr) (argKinds : Array ArgKind) (stx : Syntax) :
    TermElabM Expr := do
  withExistingLocalDecls argDecls.toList do
    let xs := argDecls.map (mkFVar ·.fvarId)
    withCopyOfNonConstVars xs argKinds fun newYs ys => do
      let zero := mkAppNBeta expr <| ← mapNonConstant xs argKinds
        fun x => do return ← mkNumeral (← inferType x) 0
      let lhs ← mkAdd (mkAppNBeta expr xs) (mkAppNBeta expr ys)
      let rhs ← mkAdd
        (mkAppNBeta expr <|
          ← (Array.zip argKinds (Array.zip xs ys)).mapM fun (kind, x, y) => do
            if kind == ArgKind.Constant then return x else mkAdd x y)
        zero
      let ty ← mkEq lhs rhs
      let add ← Elab.Term.elabTermAndSynthesizeEnsuringType stx (some ty)
      return ← mkLambdaFVars xs <| ← mkLambdaFVars newYs add

end AffineAtoms

end Elaborators

end CvxLean
