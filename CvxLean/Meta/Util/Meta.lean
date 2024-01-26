import Lean

namespace Lean.Meta

variable [MonadControlT MetaM m] [Monad m]

/-- Open lambda-expression by introducing a new local declaration. Similar to
lambdaTelescope, but for only one variable. -/
def withLambdaBody (e : Expr) (x : (fvar : Expr) → (body : Expr) → MetaM α) : MetaM α := do
  match e with
  | Expr.lam n ty body _ =>
    withLocalDeclD n ty fun fvar => do
      let body := body.instantiate1 fvar
      x fvar body
  | _ => throwError "withLambdaBody: expected lambda-expression: {e}"


def withLocalDeclsDNondep [Inhabited α] (declInfos : Array (Lean.Name × Expr))
  (k : (xs : Array Expr) → m α) : m α :=
  withLocalDeclsD (declInfos.map fun (n, t) => (n, fun _ => pure t)) k

/-- Introduce let declarations into the local context. -/
partial def withLetDecls' -- TODO: SciLean conflict.
    [Inhabited α]
    (declInfos : Array (Name × (Array Expr → m Expr) × (Array Expr → m Expr)))
    (k : (xs : Array Expr) → m α) :
    m α :=
  loop #[]
where
  loop [Inhabited α] (acc : Array Expr) : m α := do
    if acc.size < declInfos.size then
      let (name, typeCtor, valCtor) := declInfos[acc.size]!
      withLetDecl name (←typeCtor acc) (←valCtor acc) fun x => loop (acc.push x)
    else
      k acc

def runMetaMAsCoreM (x : MetaM α) : CoreM α :=
  Prod.fst <$> x.run {} {}

end Lean.Meta

namespace Lean.Meta

open Lean.Elab.Tactic Lean.Elab.Term

partial def runTactic (goal : MVarId) (tac : MVarId → TacticM (List MVarId)) :
  MetaM (List MVarId) := do
  TermElabM.run' (run goal (do replaceMainGoal <| ← tac <| ← getMainGoal))

end Lean.Meta
