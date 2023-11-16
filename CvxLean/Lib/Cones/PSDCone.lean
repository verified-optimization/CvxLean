import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Real 

def Matrix.PSDCone {m} [Fintype m] (M : Matrix m m Real) : Prop := 
  Matrix.PosSemidef M

end Real
