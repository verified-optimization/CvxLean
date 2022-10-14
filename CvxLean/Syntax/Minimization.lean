import Mathbin.Data.Real.Basic
import CvxLean.Lib.Minimization
import CvxLean.Meta.Missing.SubExpr
import CvxLean.Meta.Minimization
import CvxLean.Syntax.Parser
import CvxLean.Syntax.Options
import CvxLean.Lib.Missing.Mathlib

attribute [-instance] coeDecidableEq

namespace CvxLean

open Lean

/-- This alias for negation is used to mark a minimization problem to be pretty 
printed as maximization. -/
def maximizeNeg := @Neg.neg

namespace Elab

open Lean.Elab Lean.Elab.Term Lean.Meta Lean.Parser.Term

/-- -/
partial def decomposeBracketedBinder : Syntax → TermElabM (Array (Syntax × Syntax)) :=
  fun stx => match stx[0] with
    | `(bracketedBinder|($ids* : $ty)) => return ids.map (fun id => (id, ty.raw))
    | `(ident|$id) => return #[(id.raw, (←`(_)).raw)]

/-- -/
partial def elabVars (idents : Array Syntax) : TermElabM (Array (Lean.Name × Expr)) := do
  let idents ← idents.concatMapM decomposeBracketedBinder
  let idents ← idents.mapM fun (id, ty) => do
    match id with
      | Syntax.ident _ _ val _ => return (val, ← Term.elabTerm ty none)
      | _ => throwError "Expected identifier: {toString id}"  
  return idents

-- TODO: allow dependently typed variables?

/-- Elaborate "optimization" problem syntax. -/
@[termElab «optimization»] def elabOptmiziation : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(optimization $idents* $minOrMax:minOrMax $obj subject to $constraints ) =>
    -- Determine names and types of the variables.
    let vars ← elabVars idents
    -- Construct domain type.
    let domain := Meta.composeDomain vars.data
    -- Introduce FVar for the domain.
    withLocalDeclD `p domain fun p => do
      -- Introduce FVars for the variables
      Meta.withDomainLocalDecls domain p fun xs prs => do
        -- Elaborate objFun.
        let obj := Expr.replaceFVars (← Term.elabTerm obj.raw none) xs prs
        -- Add `maximizeNeg` constant to mark maximization problems and to negate the objective.
        let obj ← match minOrMax.raw[0]!.getKind with
        | `minimize => pure obj
        | `maximize => mkAppM ``maximizeNeg #[obj]
        | _ => throwError "expected minimize or maximize: {minOrMax.raw[0]!.getKind}"
        let obj ← mkLambdaFVars #[p] obj
        -- Elaborate constraints.
        let constraints := constraints.raw[0]!.getArgs
        let constraints ← constraints.mapM fun c => do 
          return Meta.mkLabel c[0].getId (← Term.elabTerm c[2] none)
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

/-- -/
def delabVar (e : Expr) : DelabM (Lean.Name × Term) := do
  match e with
  | Expr.mdata m e =>
    match m.get? `CvxLeanLabel with
    | some (name : Lean.Name) =>
      return (name, ← descend e 0 do delab)
    | none => failure
  | _           => return (`_, ← delab)

/-- -/
partial def delabDomain : DelabM (List (Lean.Name × Term)) := do
  let e ← getExpr
  match e with
  | Expr.app (Expr.app (Expr.const `Prod _) ty1) ty2 => do
    let stx1 ← withNaryArg 0 (do delabVar $ e.getArg! 0)
    let stx2 ← withNaryArg 1 (do delabDomain)
    return stx1 :: stx2
  | _ => return [← delabVar e]

/-- -/
partial def delabConstraint : DelabM (TSyntax ``Parser.constraint) := do
  match ← getExpr with
  | Expr.mdata m e =>
    match m.get? `CvxLeanLabel with
    | some (name : Lean.Name) =>
      return mkNode ``Parser.constraint #[(mkIdent name).raw, mkAtom ":", (← descend e 0 do delab).raw]
    | none => failure
  | _  => return (← `(Parser.constraint|_ : $(← delab)))

/-- -/
partial def delabConstraints : DelabM (List (TSyntax ``Parser.constraint)) := do
  let e ← getExpr
  match e with
  | Expr.app (Expr.app (Expr.const `And _) l) r =>
    let l : TSyntax _ ← withNaryArg 0 delabConstraint
    let r : List (TSyntax _) ← withNaryArg 1 delabConstraints
    return l :: r
  | _ => return [← delabConstraint]

/-- -/
def withDomainBinding [Inhabited α] (domain : Expr) (x : DelabM α) : DelabM α := do
  guard (← getExpr).isLambda
  withBindingBody' `p fun p => do
    withDomainLocalDecls domain p fun xs prs => do
      let e ← getExpr
      let e ← replaceProjections e p.fvarId! xs
      withExpr e do x

/-- -/
@[delab app]
partial def delabMinimization : Delab := do
  if not (pp.optMinimization.get (← getOptions)) then failure
  match ← getExpr with
  | Expr.app
      (Expr.app
        (Expr.app
          (Expr.app (Expr.const `Minimization.mk _) domain)
          codomain)
        objFun) constraints  =>
    let constraints : Array Syntax := #[]
    let idents ← withType $ withNaryArg 0 do
      let tys ← delabDomain
      let tys ← tys.mapM fun (name, stx) => do
        `(Parser.minimizationVar|($(mkIdent name) : $stx))
      return tys.toArray
    let (objFun, isMax) ← withNaryArg 2 do withDomainBinding domain do
      match ← getExpr with
      | Expr.app (Expr.app (Expr.app (Expr.const ``maximizeNeg _) _) _) e => 
        withExpr e do
          return (← delab, true)
      | _ =>
        return (← delab, false)
    let constraints := ← withNaryArg 3 do
      let cs ← withDomainBinding domain delabConstraints
      return mkNode ``Parser.constraints #[mkNullNode cs.toArray]
    if isMax then
      `(optimization $idents* maximize $objFun subject to $constraints)
    else
      `(optimization $idents* minimize $objFun subject to $constraints)
  | _ => failure

end Delab

end CvxLean
