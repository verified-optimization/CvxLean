import CvxLean.Lib.Math.Data.Real
import CvxLean.Meta.Minimization
import CvxLean.Meta.Util.Error
import CvxLean.Tactic.PreDCP.Egg.Sexp
import CvxLean.Tactic.PreDCP.Egg.EggTypes
import CvxLean.Tactic.DCP.Tree

/-!
# Strings as S-expressions to `Expr`

This file is, essentially, the reverse of `CvxLean/Tactic/PreDCP/Egg/FromMinimization`. Once `egg`
has given us a list of steps, we need to turn them into expressions to re-construct a proof. We do
that here. This is used by the `pre_dcp` tactic.
-/

namespace CvxLean

open Lean Meta

/-- Parse an S-expression into an `EggTree`. -/
partial def Sexpr.toEggTree : Sexp → MetaM EggTree
  | .atom a => return Tree.leaf a
  | .list l => do
    if l.length == 0 then
      throwPreDCPError "`Sexp` to `Tree` conversion error, unexpected empty list."
    else
      match l.head! with
      | .atom op =>
          let children ← l.tail.mapM toEggTree
          return CvxLean.Tree.node op (Array.mk children)
      | .list _ =>
          throwPreDCPError "`Sexp` to `Tree` conversion error, unexpected list as operator."

/-- Parse an string into an S-expression and, if successful, parse it into an `EggTree`. -/
def EggString.toEggTree (s : String) : MetaM EggTree := do
  match parseSingleSexp s with
  | Except.ok sexpr => Sexpr.toEggTree sexpr
  | Except.error e => throwError s!"{e}"

/-- After turning an S-expression into an `EggTree` (AST), we traverse it to turn it into a Lean
`Expr`. This mostly involves translating the constructors (as strings) into their corresponding
Lean constructors.

There are some special cases:
* Variables are translated into free variables and parameters are translated into constants.
* Constraints are composed using their tags, which are embedded into the tree.
* Numerical values are parsed into `OfScientific`s.
* In the expected sub-expression, there might be a `"?"`. This translates to a free varaible called
  `subexpr` (no optimization variable may be named `subexpr`). It is `pre_dcp`'s responsibility to
  bind this free variable appropriately (as well as the rest of free variables). -/
partial def EggTree.toExpr (vars params : List String) : EggTree → MetaM Expr
  -- Pi.
  | Tree.leaf "pi" => do
      return mkConst ``Real.pi
  -- Special case: hole. Used to apply `congrAgr` in `pre_dcp`.
  | Tree.leaf "?" => do
      if "subexpr" ∈ vars then
        throwPreDCPError "\"subexpr\" is not a valid variable name."
      return mkFVar (FVarId.mk (Name.mkSimple "subexpr"))
  -- Numbers.
  | Tree.leaf s =>
      match Json.Parser.num s.mkIterator with
      | Parsec.ParseResult.success _ res => do
          -- NOTE: not ideal, but `norm_num` should get us to where we want.
          let nnRatCastToOfScientific :=
            mkApp2 (mkConst ``NNRatCast.toOfScientific ([levelZero] : List Level))
              (mkConst ``Real) (mkConst ``Real.instNNRatCast)
          let realOfScientific :=
            mkApp2 (mkConst ``OfScientific.ofScientific [levelZero])
              (mkConst ``Real)
              nnRatCastToOfScientific
          let num := mkApp3 realOfScientific
            (mkNatLit res.mantissa.natAbs) (Lean.toExpr true) (mkNatLit res.exponent)
          let expr :=
            if res.mantissa < 0 then
              mkApp3
                (mkConst ``Neg.neg [levelZero]) (mkConst ``Real) (mkConst ``Real.instNeg) num
            else num
          let simpResult ←
            Mathlib.Meta.NormNum.deriveSimp (ctx := ← Simp.Context.mkDefault) (e := expr)
          return simpResult.expr
      | _ => throwPreDCPError "conversion error, unexpected num {s}."
  -- Variables.
  | Tree.node "var" #[Tree.leaf s] =>
      if s ∈ vars then
        return mkFVar (FVarId.mk (Name.mkSimple s))
      else
        throwPreDCPError "conversion error, unexpected var {s}."
  -- Parameters.
  | Tree.node "param" #[Tree.leaf s] =>
    if s ∈ params then
      return mkFVar (FVarId.mk (Name.mkSimple s))
    else
      return mkConst (Name.mkSimple s)
  -- Equality.
  | Tree.node "eq" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkAppN (mkConst ``Eq [levelOne]) #[(mkConst `Real), t1, t2]
  -- Less than or equal to.
  | Tree.node "le" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkAppN
        (mkConst ``LE.le [levelZero])
        #[(mkConst `Real), (mkConst ``Real.instLE), t1, t2]
  -- Negation.
  | Tree.node "neg" #[t] => do
      let t ← toExpr vars params t
      return mkAppN
        (mkConst ``Neg.neg [levelZero])
        #[(mkConst ``Real), (mkConst ``Real.instNeg), t]
  -- Inverse.
  | Tree.node "inv" #[t] => do
      let t ← toExpr vars params t
      return mkAppN
        (mkConst ``Inv.inv [levelZero])
        #[(mkConst ``Real), (mkConst ``Real.instInv), t]
  -- Absolute value.
  | Tree.node "abs" #[t] => do
      let t ← toExpr vars params t
      return mkAppN
        (mkConst ``abs [levelZero])
        #[(mkConst ``Real), (mkConst ``Real.lattice), (mkConst ``Real.instAddGroup), t]
  -- Square root.
  | Tree.node "sqrt" #[t] => do
      let t ← toExpr vars params t
      return mkAppN (mkConst ``Real.sqrt) #[t]
  -- Log.
  | Tree.node "log" #[t] => do
      let t ← toExpr vars params t
      return mkAppN (mkConst ``Real.log) #[t]
  -- Exp.
  | Tree.node "exp" #[t] => do
      let t ← toExpr vars params t
      return mkAppN (mkConst ``Real.exp) #[t]
  -- XExp.
  | Tree.node "xexp" #[t] =>
      EggTree.toExpr vars params (Tree.node "mul" #[t, Tree.node "exp" #[t]])
  -- Entr.
  | Tree.node "entr" #[t] =>
      EggTree.toExpr vars params (Tree.node "neg" #[Tree.node "mul" #[t, Tree.node "log" #[t]]])
  -- Min.
  | Tree.node "min" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkAppN
        (mkConst ``Min.min [levelZero])
        #[(mkConst ``Real), (mkConst ``Real.instMinReal), t1, t2]
  -- Max.
  | Tree.node "max" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkAppN
        (mkConst ``Max.max [levelZero])
        #[(mkConst ``Real), (mkConst ``Real.instMaxReal), t1, t2]
  -- Addition.
  | Tree.node "add" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkRealHBinAppExpr ``HAdd.hAdd ``instHAdd 1 ``Real.instAdd t1 t2
  -- Subtraction.
  | Tree.node "sub" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkRealHBinAppExpr ``HSub.hSub ``instHSub 1 ``Real.instSub t1 t2
  -- Multiplication.
  | Tree.node "mul" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkRealHBinAppExpr ``HMul.hMul ``instHMul 1 ``Real.instMul t1 t2
  -- Division.
  | Tree.node "div" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkRealHBinAppExpr ``HDiv.hDiv ``instHDiv 1 ``Real.instDivReal t1 t2
  -- Pow.
  | Tree.node "pow" #[t1, t2] => do
      let t1 ← toExpr vars params t1
      let t2 ← toExpr vars params t2
      return mkRealHBinAppExpr ``HPow.hPow ``instHPow 2 ``Real.instPow t1 t2
  -- Quad over Lin.
  | Tree.node "qol" #[t1, t2] =>
      EggTree.toExpr vars params (Tree.node "div" #[Tree.node "pow" #[t1, Tree.leaf "2"], t2])
  -- Geo mean.
  | Tree.node "geo" #[t1, t2] =>
      EggTree.toExpr vars params (Tree.node "sqrt" #[Tree.node "mul" #[t1, t2]])
  -- Log sum exp.
  | Tree.node "lse" #[t1, t2] =>
      EggTree.toExpr vars params (Tree.node "log" #[Tree.node "add" #[
        Tree.node "exp" #[t1],
        Tree.node "exp" #[t2]]])
  -- Norm2.
  | Tree.node "norm2" #[t1, t2] =>
    EggTree.toExpr vars params (Tree.node "sqrt" #[Tree.node "add" #[
      Tree.node "pow" #[t1, Tree.leaf "2"],
      Tree.node "pow" #[t2, Tree.leaf "2"]]])
  -- Constr.
  | Tree.node "constr" #[Tree.leaf s, t] => do
      let t ← toExpr vars params t
      return Meta.mkLabel (Name.mkSimple s) t
  -- Error.
  | Tree.node op children =>
      throwPreDCPError "conversion error, unexpected op {op} with {children.size} children."
where
  mkRealHBinAppExpr (opName instHName : Name) (nTyArgs : Nat) (instName : Name)
    (e1 e2 : Expr) : Expr :=
    let R := Lean.mkConst ``Real
    let inst := mkAppN (mkConst instHName (List.replicate nTyArgs levelZero))
      (Array.mk (List.replicate nTyArgs R) ++ [Lean.mkConst instName])
    mkAppN
      (mkConst opName [levelZero, levelZero, levelZero])
      #[R, R, R, inst, e1, e2]

/-- First turn a string (as a S-expression) into an `EggTree`, then call `EggTree.toExpr` to get
an expression. -/
def EggString.toExpr (vars params : List Name) (s : String) : MetaM Expr :=
  EggString.toEggTree s >>= EggTree.toExpr (vars.map toString) (params.map toString)

end CvxLean
