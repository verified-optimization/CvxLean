/-!
# Representation of numerical solution

This file defines a generic format for numerical solutions. It is currently a simplified version of
the full solution data that we obtain from solvers.
-/

namespace CvxLean

structure SimpleVarSol where
  name  : String
  value : Float

namespace SimpleVarSol

instance : ToString SimpleVarSol where
  toString v :=
    v.name ++ "* = " ++ toString v.value

end SimpleVarSol

structure SimpleMatrixVarSol where
  name  : String
  I     : Nat
  J     : Nat
  value : Option Float

namespace SimpleMatrixVarSol

instance : ToString SimpleMatrixVarSol where
  toString v :=
    match v.value with
    | some x => v.name ++ "[" ++ toString v.I ++ ", " ++ toString v.J ++ "]* = " ++ toString x
    | none   => "none"

end SimpleMatrixVarSol

structure SolutionData where
  status         : String
  varsSols       : List SimpleVarSol
  matrixVarsSols : List SimpleMatrixVarSol

namespace SolutionData

instance : ToString SolutionData where
  toString s :=
    "Status: " ++ s.status ++ "\n" ++
    "Variables: (" ++ ", ".intercalate (s.varsSols.map toString) ++ ")\n" ++
    "Matrix variables: (" ++ ", ".intercalate (s.matrixVarsSols.map toString) ++ ")"

end SolutionData

end CvxLean
