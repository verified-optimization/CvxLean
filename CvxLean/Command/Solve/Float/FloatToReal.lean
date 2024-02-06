import Mathlib.Data.Real.Basic
import CvxLean.Lib.Math.Data.Real

/-!
Conversion used in `Solve/Conic.lean` to read the solver's output into an expression to which we can
apply the backward map.
-/

namespace CvxLean

open Lean

/-- Convert a `Float` to an `Expr` of type `Real`. -/
def floatToReal (f : Float) : Expr :=
  let divisionRingToOfScientific :=
    mkApp2 (mkConst ``DivisionRing.toOfScientific ([levelZero] : List Level))
      (mkConst ``Real)
      (mkConst ``Real.instDivisionRingReal)
  let realOfScientific :=
    mkApp2 (mkConst ``OfScientific.ofScientific ([levelZero] : List Level))
      (mkConst ``Real)
      divisionRingToOfScientific
  match Json.Parser.num f.toString.mkIterator with
  | Parsec.ParseResult.success _ res =>
      let num := mkApp3 realOfScientific
        (mkNatLit res.mantissa.natAbs) (toExpr true) (mkNatLit res.exponent)
      if res.mantissa < 0 then
        mkApp3 (mkConst ``Neg.neg ([levelZero] : List Level))
          (mkConst ``Real) (mkConst ``Real.instNegReal) num
      else num
  -- On parser error return zero.
  | Parsec.ParseResult.error _ _ =>
      mkApp3 realOfScientific
        (mkConst ``Int.zero) (toExpr true) (mkNatLit 1)

end CvxLean
