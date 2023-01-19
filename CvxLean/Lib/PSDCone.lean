import Mathbin.LinearAlgebra.Matrix.PosDef

namespace Real 

def Matrix.PSDCone {m} [Fintype m] (M : Matrix m m Real) : Prop := 
  --Matrix.PosSemidef M
  -- TODO: Some issue with IsROrC
  M.IsHermitian ∧ ∀ x : m → Real, x ≠ 0 → 0 < Matrix.dotProduct x (M.mulVec x)

end Real
