import Lean
import Lean.Environment

/-!
Definitions tagged with `optimization_param` are treated differently by `solve` as it attempts to
extract its value.
-/

section OptimizationParam

open Lean

initialize optimizationParamAttr : TagAttribute ←
  registerTagAttribute `optimization_param "Optimization parameter."

def isOptimizationParam (n : Name) : MetaM Bool := do
  return optimizationParamAttr.hasTag (← getEnv) n

def getAllOptimizationParams : MetaM (List Name) := do
  return (optimizationParamAttr.ext.getState (← getEnv)).toList

def getOptimizationParamExpr (n : Name) (e : Expr) : MetaM Expr := do
  match (← getEnv).constants.find! n with
  | ConstantInfo.defnInfo defn => return defn.value
  | _ => return e

end OptimizationParam
