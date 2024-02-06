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

end SubExpr

end Lean.PrettyPrinter.Delaborator
