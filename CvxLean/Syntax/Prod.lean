import Lean

/-!
Custom syntax for projections.
-/

/-- Syntax for projections of `Prod`. For example, it allows us to write `x#3` for `x.2.2.1` and
`x#4` for `x.2.2.2`. -/
syntax (name := prodField) term "#" Lean.Parser.numLit : term

namespace Lean.Elab

open Meta Term

@[term_elab prodField]
def elabProdField : TermElab :=
  fun stx _ => do
    match stx with
    | `($e # $t) => do
        match t.raw[0]! with
        | Syntax.atom _ val =>
            let some num := val.toNat? | throwUnsupportedSyntax
            let e ← elabTerm e none
            let ty ← instantiateMVars <| ← inferType e
            return ← mkProj e ty num
        | _ => throwUnsupportedSyntax
    | _ => throwUnsupportedSyntax
where
  mkProj (e ty : Expr) (n : Nat) (recursive := false) : TermElabM Expr :=
    match ty, n with
    | (.app (.app (.const ``Prod lvls) α) β), 1 => do
        return mkApp3 (mkConst ``Prod.fst lvls) α β e
    | _, 1 =>
        if recursive then return e else throwUnsupportedSyntax
    | (.app (.app (.const ``Prod lvls) α) β), (n + 1) => do
        let esnd := mkApp3 (mkConst ``Prod.snd lvls) α β e
        mkProj esnd β n true
    | _, _ => throwUnsupportedSyntax

end Lean.Elab

namespace Lean.PrettyPrinter.Delaborator

open SubExpr

@[delab app] partial def delabProdField : Delab := do
  let (stx, n) ← aux (← getExpr)
  return ← `($(⟨stx⟩) # $(quote n))
where
  aux (top : Expr) (first : Option Bool := none) : DelabM (Syntax × Nat) := do
    /- `first` tells us whether the outermost projection was `.1` (`some true`) or
        `.2` (`some false`). If this is not a recursive call, `first` is `none`. -/
    match first, ← getExpr with
    | none, .app (.app (.app (.const ``Prod.fst _) _) _) _ => do
        withNaryArg 2 do aux top true
    | _, .app (.app (.app (.const ``Prod.snd _) _) _) _ => do
        withNaryArg 2 do
          let (stx, n) ← aux top (first == some true)
          return (stx, n + 1)
    | none, _ => failure
    | true, _ => return (← delab, 1)
    | false, _ =>
        if (← Meta.inferType top).getAppFn.isConstOf ``Prod then failure else return (← delab, 1)

end Lean.PrettyPrinter.Delaborator
