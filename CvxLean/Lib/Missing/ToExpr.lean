import Lean

section ToExpr 

open Lean

instance : ToExpr Expr where 
  toExpr e := e 
  toTypeExpr := mkConst ``Expr

instance : ToExpr Int where 
  toExpr i := 
    if i < 0 then 
      mkApp (mkConst ``Int.neg) (mkApp (mkConst ``Int.natAbs) (toExpr i.toNat))
    else 
      mkApp (mkConst ``Int.ofNat) (toExpr i.toNat)
  toTypeExpr := mkConst ``Int

instance : ToExpr Float where 
  toExpr f := 
    match Json.Parser.num f.toString.mkIterator with
    | Parsec.ParseResult.success _ res =>
        let e := 
          mkApp5 
            (mkConst ``OfScientific.ofScientific [levelZero])
            (mkConst ``Float)
            (mkConst ``instOfScientificFloat)
            (toExpr res.mantissa.natAbs)
            (toExpr true)
            (toExpr res.exponent)
        if res.mantissa < 0 then 
          mkApp (mkConst ``Float.neg) e 
        else 
          e 
    | Parsec.ParseResult.error it err  => 
        mkApp (mkConst ``Float.ofNat) (toExpr (0 : Nat))
  toTypeExpr := mkConst ``Float

instance {n} : ToExpr (Fin n) where 
  toExpr x := 
    mkApp (mkConst ``Fin.ofNat) (toExpr x.val)
  toTypeExpr := mkApp (mkConst ``Fin) (toExpr n)

instance : ToExpr (Array Float) := by infer_instance

instance : ToExpr (Array (Array Float)) := by infer_instance

end ToExpr 
