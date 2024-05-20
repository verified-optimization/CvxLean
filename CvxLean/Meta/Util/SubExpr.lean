import Lean

/-!
Delaborator helper functions.
-/

namespace Lean.PrettyPrinter.Delaborator

namespace SubExpr

variable {α : Type} [Inhabited α]
variable {m : Type → Type} [Monad m]

variable [MonadReaderOf SubExpr m] [MonadWithReaderOf SubExpr m]
variable [MonadLiftT MetaM m] [MonadControlT MetaM m]
variable [MonadLiftT IO m]

/-- Pretend that we actually want to delaborate the given expression. -/
def withExpr (e : Expr) (x : m α) : m α := do
  withTheReader SubExpr (fun cfg => { cfg with expr := e, pos := cfg.pos }) x

/-- Old version of `withBindingBody'`, needed for parsing.
TODP: Why does `withBindingBody' (x := pure)` not work? -/
def withBindingBody'' {α : Type} {m : Type → Type} [Monad m] [MonadReaderOf SubExpr m]
    [MonadWithReaderOf SubExpr m] [MonadControlT MetaM m] (n : Name) (x : Expr → m α) : m α := do
  let e ← getExpr
  Meta.withLocalDecl n e.binderInfo e.bindingDomain! fun fvar =>
    descend (e.bindingBody!.instantiate1 fvar) 1 (x fvar)

end SubExpr

end Lean.PrettyPrinter.Delaborator
