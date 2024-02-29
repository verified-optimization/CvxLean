import Lean
import CvxLean.Lib.Math.Data.Array

/-!
Helper functions to create and manipulate Lean expressions.
-/

namespace Lean

open Lean Meta

namespace Expr

/-- Given expressions `e₁, ..., eₙ` return `(And.intro e₁ ⋯ (And.intro eₙ₋₁ eₙ) ⋯)`, i.e., `∧` them,
with associativity to the right. -/
def mkAndIntro (xs : Array Expr) : MetaM Expr := do
  let mut res := xs[xs.size - 1]!
  for i in [:xs.size - 1] do
    res ← mkAppM ``And.intro #[xs[xs.size - 2 - i]!, res]
  return res

/-- Make existential type. -/
def mkExistsFVars (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut res := e
  for i in [:xs.size] do
    let x := xs[xs.size - i - 1]!
    res ← mkAppM ``Exists #[← mkLambdaFVars #[x] res]
  return res

/-- Make existential term. -/
def mkExistsIntro (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut res := e
  for i in [:xs.size] do
    let x := xs[xs.size - i - 1]!
    res ← mkAppOptM ``Exists.intro
      #[none, some <| ← mkLambdaFVars #[x] (← inferType res), some x, some res]
  return res

/-- Make let bindings from free variables `xs`. -/
def mkLetFVarsWith (e : Expr) (xs : Array Expr) (ts : Array Expr) : MetaM Expr := do
  if xs.size != ts.size then
    throwError "Expected same length: {xs} and {ts}"
  let mut e := e.abstract xs
  for i in [:xs.size] do
    let n := (← FVarId.getDecl xs[xs.size - 1 - i]!.fvarId!).userName
    e := mkLet n (← inferType xs[xs.size - 1 - i]!) ts[xs.size - 1 - i]! e
  return e

/-- Check if `e` is constant by checking if it contains any free variable. -/
def isConstant (e : Expr) : Bool := (Lean.collectFVars {} e).fvarSet.isEmpty

/-- Check if `e` is constant by checking if it contains any free variable from `vars`. -/
def isRelativelyConstant (e : Expr) (vars : Array FVarId) : Bool := Id.run do
  let fvarSet := (Lean.collectFVars {} e).fvarSet
  for v in vars do
    if fvarSet.contains v then return false
  return true

/-- Remove the metadata from an expression. -/
def removeMData (e : Expr) : CoreM Expr := do
  let post (e : Expr) : CoreM TransformStep := do
    return TransformStep.done e.consumeMData
  Core.transform e (post := post)

/-- Basically `β`-reduction. -/
def mkAppBeta (e : Expr) (arg : Expr) :=
  e.bindingBody!.instantiate1 arg

/-- Same as `mkAppBeta` but with several arguments. -/
def mkAppNBeta (e : Expr) (args : Array Expr) : Expr := Id.run do
  let mut e := e
  for _ in args do
    e := e.bindingBody!
  e.instantiateRev args

/-- Given a lambda term `e := λx₁. ... λxₙ. b` and values for every variable `xᵢ`, turn `e` into
`let x₁ := v₁; ... let xₙ := vₙ; b`. -/
def convertLambdasToLets (e : Expr) (args : Array Expr) : Expr := Id.run do
  let mut e := e
  let mut names := #[]
  let mut tys := #[]
  for _ in args do
    tys := tys.push e.bindingDomain!
    names := names.push e.bindingName!
    e := e.bindingBody!
  for i in [:args.size] do
    e := mkLet names[args.size - 1 - i]! tys[args.size - 1 - i]! args[args.size - 1 - i]! e
  return e

/-- Size of expressions, which can be a useful heuristic. -/
def size : Expr → Nat
  | bvar _          => 1
  | fvar _          => 1
  | mvar _          => 1
  | sort _          => 1
  | const _ _       => 1
  | app a b         => size a + size b
  | lam _ _ a _     => size a + 1
  | forallE _ _ a _ => size a + 1
  | letE _ _ a b _  => size a + size b + 1
  | lit _           => 1
  | mdata _ a       => size a
  | proj _ _ a      => size a + 1

open Meta

/-- Make a product of expressions. -/
def mkProd (as : Array Expr) : MetaM Expr :=
  if as.size == 0 then
    throwError "Empty list."
  else if as.size == 1 then
    return as[0]!
  else
    Array.foldrM
      (fun e1 e2 => Lean.Meta.mkAppM ``Prod.mk #[e1, e2]) as[as.size - 1]! (as.take (as.size - 1))

private def mkArrayAux (ty : Expr) (as : List Expr) :
    MetaM Expr := do
  match as with
  | []    => return mkAppN (mkConst ``Array.empty [levelZero]) #[ty]
  | e::es =>
      let r ← mkArrayAux ty es
      mkAppM ``Array.push #[r, e]

/-- Make expression array of given type, from array of expressions. -/
def mkArray (ty : Expr) (as : Array Expr) : MetaM Expr :=
  mkArrayAux ty as.data.reverse

end Expr

namespace Elab.Term

/-- Combination of `elabTermAndSynthesize` and `ensureHasType`. -/
def elabTermAndSynthesizeEnsuringType (stx : Syntax) (expectedType? : Option Expr)
    (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  let e ← elabTermAndSynthesize stx expectedType?
  withRef stx <| ensureHasType expectedType? e errorMsgHeader?

end Elab.Term

/-- Wrapper of `Lean.addAndCompile` for definitions with some default values. -/
def Lean.simpleAddAndCompileDefn (n : Name) (e : Expr) : MetaM Unit := do
  Lean.addAndCompile <|
    Declaration.defnDecl <|
      mkDefinitionValEx n [] (← inferType e) e (Lean.ReducibilityHints.regular 0)
      (DefinitionSafety.safe) []

/-- Wrapper of `Lean.addDecl` for definitions with some default values. -/
def Lean.simpleAddDefn (n : Name) (e : Expr) : MetaM Unit := do
  Lean.addDecl <|
    Declaration.defnDecl <|
      mkDefinitionValEx n [] (← inferType e) e (Lean.ReducibilityHints.regular 0)
      (DefinitionSafety.safe) []

end Lean
