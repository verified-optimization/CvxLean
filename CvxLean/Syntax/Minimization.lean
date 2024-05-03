import CvxLean.Lib.Minimization
import CvxLean.Meta.Util.SubExpr
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Minimization
import CvxLean.Syntax.Parser

/-!
# Syntax to define optimization problems

This file defines how the custom optimization syntax is elaborated into a `Minimization` term. This
involves encoding variable names and constraint tags in the metadata. Variable names also tell us
how to replace their occurrences by the appropriate projection. We illustrate it with an example.
```
optimization (x y : ℝ)
    minimize 40 * x + 30 * y
    subject to
      c₁ : 12 ≤ x + y
      c₂ : 16 ≤ 2 * x + y
```
is elaborated into
```
Minimization.mk
  (fun p => 40 * p.1 + 30 * p.2)
  (fun p => 12 ≤ p.1 + p.2 ∧ 16 ≤ 2 * p.1 + p.2)
```
The full version with labels would be
```
@Minimization.mk ({** ℝ ** `x **} × {** ℝ ** `y **}) ℝ
  (fun p => 40 * p.1 + 30 * p.2)
  (fun p => {** 12 ≤ p.1 + p.2 ** `c₁ **} ∧ {** 16 ≤ 2 * p.1 + p.2 ** `c₂ **})
```
where the `{ ** e ** n }` notation is as defined in `CvxLean/Syntax/Label.lean`.

We also define how to delaborate it so that it can be pretty printed back to the custom syntax.
-/

namespace CvxLean

open Lean

/-- This alias for negation is used to mark a minimization problem to be pretty printed as
maximization. -/
def maximizeNeg := @Neg.neg

namespace Elab

open Lean.Elab Lean.Elab.Term Lean.Meta Lean.Parser.Term

/-- Helper function for `elabVars`. -/
private def decomposeBracketedBinder : Syntax → TermElabM (Array (Syntax × Syntax)) :=
  fun stx => match stx[0] with
    | `(bracketedBinderF|($ids* : $ty)) => return ids.map (·.raw, ty.raw)
    | `(ident|$id) => return #[(id.raw, (← `(_)).raw)]

/-- Get the names and types of the variables after the `optimization` keyword. -/
def elabVars (idents : Array (TSyntax `CvxLean.Parser.minimizationVar)) :
    TermElabM (Array (Lean.Name × Expr)) := do
  let idents ← idents.concatMapM decomposeBracketedBinder
  let idents ← idents.mapM fun (id, ty) => do
    match id with
      | Syntax.ident _ _ val _ => return (val, ← Term.elabTerm ty none)
      | _ => throwParserError "expected identifier got {id}."
  return idents

/-- Extract names of "let" expressions after `with`. -/
def preElabLetVars (letVars : Array (TSyntax `CvxLean.Parser.letVar)) :
    TermElabM (Array (Lean.Name × TSyntax `Lean.Parser.Term.letDecl)) := do
  letVars.mapM fun stx =>
    match stx with
      | `(CvxLean.Parser.letVar| with $letD:letDecl) =>
          match letD with
          | `(letDecl| $id:ident := $_) => return (id.getId, letD)
          | _ => throwParserError "expected identified let declaration got {letD}."
      | _ => throwParserError "expected let declaration got {stx}."

/-- Extract names and terms of constraints. We do it in two steps so that we can insert lets if
needed. -/
def preElabConstraints (constraints : TSyntax `CvxLean.Parser.constraints) :
    TermElabM (Array (Lean.Name × TSyntax `term)) := do
  match constraints with
  | `(CvxLean.Parser.constraints| $constrs*) => do
      constrs.mapM fun cDecl =>
        match cDecl with
          | `(CvxLean.Parser.constraint| $id:ident : $c) => return (id.getId, c)
          | `(CvxLean.Parser.constraint| _ : $c) => return (Name.anonymous, c)
          | _ => throwParserError "expected constraint got {cDecl}."
  | _ => throwParserError "expected constraints got {constraints}."

macro_rules
| `(optimization $idents* $minOrMax:minOrMax $obj) =>
    `(optimization $idents* $minOrMax:minOrMax $obj subject to _ : True)

-- TODO: allow dependently typed variables?

/-- Collect all identifiers that appear in some syntax. -/
partial def _root_.Lean.Syntax.gatherIdents : Syntax → Array Lean.Name
  | .missing => #[]
  | .ident _ _ n _ => #[n]
  | .atom _ _ => #[]
  | .node _ _ stxs => stxs.foldl (init := #[]) fun acc stx => acc ++ stx.gatherIdents

/-- Elaborate `optimization` problem syntax, building a term of type `Minimization D R`.  -/
@[term_elab «optimization»] def elabOptmiziation : Term.TermElab := fun stx _expectedType? => do
  match stx with
  | `(optimization $idents* $lets:letVar* $minOrMax:minOrMax $obj subject to $constraints) =>
      -- Determine names and types of the variables.
      let vars ← elabVars idents
      -- Construct domain type.
      let domain := Meta.composeDomain vars.data
      -- Construct let vars syntax.
      let letsStx ← preElabLetVars lets
      -- Introduce FVar for the domain.
      withLocalDeclD `p domain fun p => do
        -- Introduce FVars for the variables
        Meta.withDomainLocalDecls domain p fun xs prs => do
          -- Elaborate objFun.
          let mut objStx := obj
          let objIdents := Syntax.gatherIdents objStx
          if letsStx.size > 0 then
            for (letVar, letD) in letsStx do
              if letVar ∈ objIdents then
                objStx := ← `(let $letD:letDecl; $objStx)
          let mut obj := Expr.replaceFVars (← Term.elabTerm objStx.raw none) xs prs
          -- Add `maximizeNeg` constant to mark maximization problems and to negate the objective.
          let minOrMaxStx := minOrMax.raw[0]!
          if minOrMaxStx.isOfKind `maximize then
            obj ← mkAppM ``maximizeNeg #[obj]
          else if !(minOrMaxStx.isOfKind `minimize) then
            throwParserError "expected minimize or maximize, got: {minOrMaxStx.getKind}"
          obj ← mkLambdaFVars #[p] obj
          -- Elaborate constraints.
          let constraints ← preElabConstraints constraints
          let constraints ← constraints.mapM fun (n, cStx) => do
            let mut cStx := cStx
            let cIdents := Syntax.gatherIdents cStx
            if letsStx.size > 0 then
              for (letVar, letD) in letsStx do
                if letVar ∈ cIdents then
                  cStx := ← `(let $letD:letDecl; $cStx)
            return Meta.mkLabel n (← Term.elabTerm cStx none)
          let constraints ← mkLambdaFVars #[p] $
            Expr.replaceFVars (Meta.composeAnd constraints.data) xs prs
          -- Put it all together.
          let res ← mkAppM ``Minimization.mk #[obj, constraints]
          check res
          return ← instantiateMVars res
  | _ => throwUnsupportedSyntax

end Elab

namespace Delab

open Lean Lean.PrettyPrinter.Delaborator SubExpr Meta

/-- Show label in an expression. -/
def delabVar (e : Expr) : DelabM (Lean.Name × Term) := do
  match e with
  | Expr.mdata m e =>
      match m.get? `CvxLeanLabel with
      | some (name : Lean.Name) => return (name, ← descend e 0 do delab)
      | none => Alternative.failure
  | _ => return (`_, ← delab)

/-- Show labels (variable names) and terms (types) in a domain type. -/
partial def delabDomain : DelabM (List (Lean.Name × Term)) := do
  let e ← getExpr
  match e with
  | Expr.app (Expr.app (Expr.const `Prod _) _ty1) _ty2 => do
      let stx1 ← withNaryArg 0 (do delabVar <| e.getArg! 0)
      let stx2 ← withNaryArg 1 (do delabDomain)
      return stx1 :: stx2
  | _ => return [← delabVar e]

/-- Show constraint with label if it has one. -/
partial def delabConstraint : DelabM (TSyntax ``Parser.constraint) := do
  match ← getExpr with
  | Expr.mdata m e =>
      match m.get? `CvxLeanLabel with
      | some (name : Lean.Name) =>
          return mkNode ``Parser.constraint
            #[(mkIdent name).raw, mkAtom ":", (← descend e 0 do delab).raw]
      | none => Alternative.failure
  | _  => return (← `(Parser.constraint|_ : $(← delab)))

/-- Show all constraints with their labels. -/
partial def delabConstraints : DelabM (List (TSyntax ``Parser.constraint)) := do
  let e ← getExpr
  match e with
  | Expr.app (Expr.app (Expr.const `And _) _l) _r =>
      let l : TSyntax _ ← withNaryArg 0 delabConstraint
      let r : List (TSyntax _) ← withNaryArg 1 delabConstraints
      return l :: r
  | _ => return [← delabConstraint]

/-- Delaborate with variable names replaced. -/
def withDomainBinding {α} [Inhabited α] (domain : Expr) (x : DelabM α) : DelabM α := do
  guard (← getExpr).isLambda
  withBindingBody' (x := pure) `p fun p => do
    withDomainLocalDecls domain p fun xs _prs => do
      let e ← getExpr
      let e ← replaceProjections e p.fvarId! xs
      withExpr e do x

/-- Show minimization problem using the custom syntax, with variable names and constraitn tags. -/
@[delab app]
partial def delabMinimization : Delab := do
  --if !(pp.opt.get (← getOptions)) then Alternative.failure
  match ← getExpr with
  | .app (.app (.app (.app (.const `Minimization.mk _) domain) _codomain) _objFun) constraints =>
      let idents ← withType <| withNaryArg 0 do
        let tys ← delabDomain
        let tys ← tys.mapM fun (name, stx) => do `(Parser.minimizationVar| ($(mkIdent name) : $stx))
        return tys.toArray
      let (objFun, isMax) ← withNaryArg 2 do withDomainBinding domain do
        match ← getExpr with
        | .app (.app (.app (.const ``maximizeNeg _) _) _) e =>
            withExpr e do
              return (← delab, true)
        | _ =>
            return (← delab, false)
      let noConstrs ← withLambdaBody constraints fun _ constrsBody => do
        isDefEq constrsBody (mkConst ``True)
      let constraints := ← withNaryArg 3 do
        let cs ← withDomainBinding domain delabConstraints
        return mkNode ``Parser.constraints #[mkNullNode <| cs.toArray.map (·.raw)]
      if noConstrs then
        if isMax then
          `(optimization $idents* maximize $objFun)
        else
          `(optimization $idents*  minimize $objFun)
      else
        if isMax then
          `(optimization $idents* maximize $objFun subject to $constraints)
        else
          `(optimization $idents* minimize $objFun subject to $constraints)
  | _ => Alternative.failure

end Delab

end CvxLean
