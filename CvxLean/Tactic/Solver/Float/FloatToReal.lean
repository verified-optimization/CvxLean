import Lean

import Mathbin.Data.Real.Basic

import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Missing.Mathlib

open Lean 

def floatToRealExpr (f : Float) : Expr :=
  let realOfScientific := 
    mkApp2 (mkConst ``OfScientific.ofScientific [levelZero])
      (mkConst ``Real)
      (mkConst ``Real.instOfScientificReal)
  match Json.Parser.num f.toString.mkIterator with
    | Parsec.ParseResult.success _ res =>
        let x := mkApp3 realOfScientific
          (mkNatLit res.mantissa.natAbs)
          (toExpr true)
          (mkNatLit res.exponent)
        if res.mantissa < 0 then 
          mkApp3 (mkConst ``Neg.neg [levelZero]) 
            (mkConst ``Real) 
            (mkConst ``Real.hasNeg)
            x
        else 
          x 
    -- On Error return zero.
    | Parsec.ParseResult.error _ _ => 
        mkApp3 realOfScientific
          (mkConst ``Int.zero) 
          (toExpr true) 
          (mkNatLit 1)
