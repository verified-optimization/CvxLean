import Lean

import CvxLean.Lib.Math.Data.Array

open Lean

/-- TODO Check if `expr` is constant by checking if it contains any free variable
from `vars`. -/
def Lean.Expr.isConstant (expr : Expr) : Bool := (Lean.collectFVars {} expr).fvarSet.isEmpty

/-- Check if `expr` is constant by checking if it contains any free variable
from `vars`. -/
def Lean.Expr.isRelativelyConstant (expr : Expr) (vars : Array FVarId) : Bool := Id.run do
  let fvarSet := (Lean.collectFVars {} expr).fvarSet
  for v in vars do
    if fvarSet.contains v then return false
  return true

def Lean.Expr.removeMData (e : Expr) : CoreM Expr := do
  let post (e : Expr) : CoreM TransformStep := do
    return TransformStep.done e.consumeMData
  Core.transform e (post := post)

def Lean.Elab.Term.elabTermAndSynthesizeEnsuringType (stx : Syntax)
  (expectedType? : Option Expr) (errorMsgHeader? : Option String := none) :
  TermElabM Expr := do
  let e ← elabTermAndSynthesize stx expectedType?
  withRef stx <| ensureHasType expectedType? e errorMsgHeader?

def mkAppBeta (e : Expr) (arg : Expr) := e.bindingBody!.instantiate1 arg

def mkAppNBeta (e : Expr) (args : Array Expr) : Expr := Id.run do
  let mut e := e
  for _arg in args do
    e := e.bindingBody!
  e.instantiateRev args

def convertLambdasToLets (e : Expr) (args : Array Expr) : Expr := Id.run do
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
