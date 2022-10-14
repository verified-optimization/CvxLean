import CvxLean.Lib.Missing.Matrix
import CvxLean.Lib.Missing.Real
import Mathbin.Data.Fintype.Basic
import Optbin.Missing.LinearAlgebra.Matrix.PosDef

namespace Real 

def Matrix.PSDCone {m} [Fintype m] (M : Matrix m m ℝ) : Prop := 
  Matrix.PosSemidef M

end Real
