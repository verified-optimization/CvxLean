import Lean
import CvxLean.Syntax.Options

/-!
# Labels for named expressions

To keep track of the names of optimization variables and the constraints, we use metadata and attach
a `CvxLeanLabel` with a name.
-/

namespace CvxLean

open Lean

syntax (name := namedConstraint) "{** " term " ** " ident " **}" : term

namespace Meta

/-- Attach a CvxLean label to an expression. They are used to indicate variable names in a domain
type and names of constraints. -/
def mkLabel (name : Name) (e : Expr) : Expr :=
  mkMData (MData.empty.setName `CvxLeanLabel name) e

variable {m} [MonadControlT MetaM m] [Monad m]

/-- Get the name and expression from metadata labelled with `CvxLeanLabel`. -/
def decomposeLabel (e : Expr) : m (Name × Expr) := do
  match e with
  | Expr.mdata m e =>
      match m.get? `CvxLeanLabel with
      | some (name : Name) => return (name, e)
      | none => decomposeLabel e
  | _ => return (`_, e)

/-- Like `CvxLean.Meta.decomposeLabel` but only returns the label name. -/
def getLabelName (e : Expr) : m Name := do
  return (← decomposeLabel e).1

end Meta

namespace Elab

open Lean.Elab

/-- Notation for attaching a name label to a term. -/
@[term_elab namedConstraint]
def elabNamedConstraint : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `({** $t ** $id **}) =>
      match id.raw with
      | Syntax.ident _ _ val _ =>
          let e ← Term.elabTerm t expectedType?
          return Meta.mkLabel val e
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

end Elab

namespace Delab

open Lean.PrettyPrinter.Delaborator SubExpr

/-- Display labelled terms using the `{** term ** name **}` syntax. -/
@[delab mdata] def delabNamedConstraint : Delab := do
  -- Omit delaboration if pretty printing option is disabled.
  if not (pp.labels.get (← getOptions)) then failure
  -- Check if `CvxLeanLabel` metadata is attached to current expression.
  let Expr.mdata m e ← getExpr | unreachable!
  match m.get? `CvxLeanLabel with
  | some (name : Name) =>
      let stx ← descend e 0 (do delab)
      let id := mkIdent name
      `({** $stx ** $id**})
  | none => failure

end Delab

end CvxLean
