import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Missing.Matrix
import CvxLean.Meta.Missing.Expr
import CvxLean.Meta.Missing.Meta

namespace CvxLean

open Lean Lean.Meta

unsafe def inferDimension (ty : Expr) : MetaM (List (Nat × Nat)) :=
  match ty.consumeMData with
  | Expr.const ``Real _ => 
      return [(1, 1)]
  | Expr.forallE _ (Expr.app (Expr.const ``Fin _) nExpr) e _ => 
    match e with 
    | Expr.const ``Real _  => do
        let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
        return [(n, 1)]
    | Expr.forallE _ (Expr.app (Expr.const ``Fin _) mExpr) (Expr.const ``Real _) _ => do 
        let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
        let m : Nat ← evalExpr Nat (mkConst ``Nat) mExpr
        return [(n, m)]
    | _ => throwError "Unsupported type: {ty}"
  | Expr.app (Expr.app (Expr.app M FinN) FinM) R => do 
    match (M, FinN, FinM, R) with 
    | (Expr.const ``Matrix _, 
      Expr.app (Expr.const ``Fin _) nExpr, 
      Expr.app (Expr.const ``Fin _) mExpr,
      Expr.const ``Real _) => 
        let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
        let m : Nat ← evalExpr Nat (mkConst ``Nat) mExpr
        return [(n, m)]
    | _ => throwError "Unsupported type: {ty}"
  | Expr.app (Expr.app (Expr.const ``Prod _) tyl) tyr => do
    let l ← inferDimension tyl
    let r ← inferDimension tyr
    return (l ++ r)
  | _ => throwError "Unsupported type: {ty}"

end CvxLean
