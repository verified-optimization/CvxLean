import Lean
import CvxLean.Lib.Math.Data.Array

/-!
Helper functions to create and manipulate Lean expressions.
-/

open Lean

/-- Check if `e` is constant by checking if it contains any free variable. -/
def Lean.Expr.isConstant (e : Expr) : Bool := (Lean.collectFVars {} e).fvarSet.isEmpty

/-- Check if `e` is constant by checking if it contains any free variable from `vars`. -/
def Lean.Expr.isRelativelyConstant (e : Expr) (vars : Array FVarId) : Bool := Id.run do
  let fvarSet := (Lean.collectFVars {} e).fvarSet
  for v in vars do
    if fvarSet.contains v then return false
  return true

/-- Remove the metadata from an expression. -/
def Lean.Expr.removeMData (e : Expr) : CoreM Expr := do
  let post (e : Expr) : CoreM TransformStep := do
    return TransformStep.done e.consumeMData
  Core.transform e (post := post)

/-- Combination of `elabTermAndSynthesize` and `ensureHasType`. -/
def Lean.Elab.Term.elabTermAndSynthesizeEnsuringType (stx : Syntax) (expectedType? : Option Expr)
    (errorMsgHeader? : Option String := none) : TermElabM Expr := do
  let e ← elabTermAndSynthesize stx expectedType?
  withRef stx <| ensureHasType expectedType? e errorMsgHeader?

def Lean.Expr.mkAppBeta (e : Expr) (arg : Expr) :=
  e.bindingBody!.instantiate1 arg

def Lean.Expr.mkAppNBeta (e : Expr) (args : Array Expr) : Expr := Id.run do
  let mut e := e
  for _arg in args do
    e := e.bindingBody!
  e.instantiateRev args

def Lean.Expr.convertLambdasToLets (e : Expr) (args : Array Expr) : Expr := Id.run do
  let mut e := e
  let mut names := #[]
  let mut tys := #[]
  for _arg in args do
    tys := tys.push e.bindingDomain!
    names := names.push e.bindingName!
    e := e.bindingBody!
  for i in [:args.size] do
    e := mkLet names[args.size-1-i]! tys[args.size-1-i]! args[args.size-1-i]! e
  return e

def Lean.Expr.size : Expr → Nat
  | bvar _        => 1
  | fvar _        => 1
  | mvar _        => 1
  | sort _        => 1
  | const _ _     => 1
  | app a b       => size a + size b
  | lam _ _ a _     => size a + 1
  | forallE _ _ a _ => size a + 1
  | letE _ _ a b _  => size a + size b + 1
  | lit _           => 1
  | mdata _ a       => size a
  | proj _ _ a      => size a + 1

open Meta

def Lean.Expr.mkProd (as : Array Expr) : MetaM Expr :=
  if as.size == 0 then
    throwError "Empty list."
  else if as.size == 1 then
    return as[0]!
  else
    Array.foldrM
      (fun e1 e2 => Lean.Meta.mkAppM ``Prod.mk #[e1, e2])
      as[as.size - 1]!
      (as.take (as.size - 1))

private def Lean.Expr.mkArrayAux (ty : Expr) (as : List Expr) :
    MetaM Expr := do
  match as with
  | []    => return mkAppN (mkConst ``Array.empty [levelZero]) #[ty]
  | e::es =>
      let r ← Lean.Expr.mkArrayAux ty es
      mkAppM ``Array.push #[r, e]

def Lean.Expr.mkArray (ty : Expr) (as : Array Expr) : MetaM Expr :=
  Lean.Expr.mkArrayAux ty as.data.reverse

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
