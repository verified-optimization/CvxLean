import Lean
import Lean.Environment

section OptimizationParam

open Lean

initialize optimizationParamAttr : TagAttribute ← 
  registerTagAttribute `optimizationParam "Optimization parameter."

def isOptimizationParam (n : Name) : MetaM Bool := do 
  return optimizationParamAttr.hasTag (← getEnv) n

def getOptimizationParamExpr (n : Name) (e : Expr) : MetaM Expr := do 
  match (← getEnv).constants.find! n with 
  | ConstantInfo.defnInfo defn => return defn.value
  | _ => return e

end OptimizationParam 
