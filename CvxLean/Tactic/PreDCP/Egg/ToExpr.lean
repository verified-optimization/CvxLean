import CvxLean.Lib.Missing.Real
import CvxLean.Meta.Minimization
import CvxLean.Tactic.PreDCP.Egg.Sexp
import CvxLean.Tactic.DCP.Tree

namespace CvxLean

section Egg.ToExpr

open Lean Meta

/-- -/
partial def Sexpr.toEggTree : Sexp → MetaM (Tree String String)
  | .atom a => return Tree.leaf a
  | .list l => do
    if l.length == 0 then
      throwError "Sexp to Tree conversion error: unexpected empty list."
    else
      match l.head! with
      | .atom op =>
        let children ← l.tail.mapM toEggTree
        return CvxLean.Tree.node op (Array.mk children)
      | .list _ => throwError "Sexp to Tree conversion error: unexpected list as operator."

def EggString.toEggTree (s : String) : MetaM (Tree String String) := do
  match parseSingleSexp s with
  | Except.ok sexpr => Sexpr.toEggTree sexpr
  | Except.error e => throwError s!"{e}"

noncomputable instance Real.instDivReal : Div ℝ :=
  by infer_instance

/-- -/
partial def EggTree.toExpr (vars : List String) : Tree String String → MetaM Expr
  -- Numbers.
  | Tree.leaf s =>
    match Json.Parser.num s.mkIterator with
    | Parsec.ParseResult.success _ res => do
      -- NOTE: This is not ideal, but it works if we use norm_num all the
      -- time.
      let divisionRingToOfScientific :=
        mkApp2 (mkConst ``DivisionRing.toOfScientific [levelZero])
          (mkConst ``Real)
          (mkConst ``Real.instDivisionRingReal)
      let realOfScientific :=
        mkApp2 (mkConst ``OfScientific.ofScientific [levelZero])
          (mkConst ``Real)
          divisionRingToOfScientific
      let num := mkApp3 realOfScientific
        (mkNatLit res.mantissa.natAbs) (Lean.toExpr true) (mkNatLit res.exponent)
      if res.mantissa < 0 then
        return mkApp3 (mkConst ``Neg.neg [levelZero])
          (mkConst ``Real) (mkConst ``Real.instNegReal) num
      else
        return num
    | _ => throwError "Tree to Expr conversion error: unexpected num {s}."
  -- Variables.
  | Tree.node "var" #[Tree.leaf s] =>
    if s ∈ vars then
      return mkFVar (FVarId.mk (Name.mkSimple s))
    else
      throwError "Tree to Expr conversion error: unexpected var {s}."
  -- Parameters.
  | Tree.node "param" #[Tree.leaf s] =>
    return mkConst (Name.mkSimple s)
  -- Equality.
  | Tree.node "eq" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkAppN (mkConst ``Eq [levelOne]) #[(mkConst `Real), t1, t2]
  -- Less than or equal to.
  | Tree.node "le" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkAppN
      (mkConst ``LE.le [levelZero])
      #[(mkConst `Real), (mkConst `Real.instLEReal), t1, t2]
  -- Negation.
  | Tree.node "neg" #[t] => do
    let t ← toExpr vars t
    return mkAppN
      (mkConst ``Neg.neg [levelZero])
      #[(mkConst ``Real), (mkConst ``Real.instNegReal), t]
  -- Square root. 
  | Tree.node "sqrt" #[t] => do
    let t ← toExpr vars t
    return mkAppN (mkConst ``Real.sqrt) #[t]
  -- Addition.
  | Tree.node "add" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkRealHBinAppExpr ``HAdd.hAdd ``instHAdd 1 ``Real.instAddReal t1 t2
  -- Subtraction.
  | Tree.node "sub" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkRealHBinAppExpr ``HSub.hSub ``instHSub 1 ``Real.instSubReal t1 t2
  -- Multiplication.
  | Tree.node "mul" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkRealHBinAppExpr ``HMul.hMul ``instHMul 1 ``Real.instMulReal t1 t2
  -- Division.
  | Tree.node "div" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkRealHBinAppExpr ``HDiv.hDiv ``instHDiv 1 ``Real.instDivReal t1 t2
  -- Log.
  | Tree.node "log" #[t] => do
    let t ← toExpr vars t
    return mkAppN (mkConst ``Real.log) #[t]
  -- Exp.
  | Tree.node "exp" #[t] => do
    let t ← toExpr vars t
    return mkAppN (mkConst ``Real.exp) #[t]
  -- Pow.
  | Tree.node "pow" #[t1, t2] => do
    let t1 ← toExpr vars t1
    let t2 ← toExpr vars t2
    return mkRealHBinAppExpr ``HPow.hPow ``instHPow 2 ``Real.instPowReal t1 t2
  -- Constr.
  | Tree.node "constr" #[Tree.leaf s, t] => do
    let t ← toExpr vars t
    return Meta.mkLabel (Name.mkSimple s) t
  -- Error.
  | Tree.node op children =>
    throwError "Tree to Expr conversion error: unexpected op {op} with {children.size} children."
where
  mkRealHBinAppExpr (opName instHName : Name) (nTyArgs : Nat) (instName : Name)
    (e1 e2 : Expr) : Expr :=
    let R := Lean.mkConst ``Real
    let inst := mkAppN (mkConst instHName (List.replicate nTyArgs levelZero))
      (Array.mk (List.replicate nTyArgs R) ++ [Lean.mkConst instName])
    mkAppN
      (mkConst opName [levelZero, levelZero, levelZero])
      #[R, R, R, inst, e1, e2]

/-- -/
def EggString.toExpr (vars : List Name) (s : String) : MetaM Expr :=
  EggString.toEggTree s >>= EggTree.toExpr (vars.map toString)

end Egg.ToExpr

end CvxLean
