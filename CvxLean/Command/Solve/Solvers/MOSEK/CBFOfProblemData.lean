import CvxLean.Lib.Math.Data.Real
import CvxLean.Meta.Minimization
import CvxLean.Meta.Util.Error
import CvxLean.Command.Solve.Data.ProblemData
import CvxLean.Command.Solve.Solvers.MOSEK.CBF

/-!
Convert a `CBF.Problem` to a `ProblemData`. The main definition is `CBF.ofProblemData`.
-/

namespace CvxLean

open Lean Meta

/-- Given thet type of the domain return the dimensions of each component. For example, for
`ℝ × (Fin n → ℝ) × (Matrix (Fin m) (Fin k) ℝ)`, return `[(1, 1), (n, 1), (m, k)]` -/
unsafe def inferDimension (ty : Expr) : MetaM (List (Nat × Nat)) :=
  match ty.consumeMData with
  | .const ``Real _ =>
      return [(1, 1)]
  | .forallE _ (.app (.const ``Fin _) nExpr) e _ =>
    match e with
    | .const ``Real _  => do
      let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
      return [(n, 1)]
    | .forallE _ (.app (.const ``Fin _) mExpr) (.const ``Real _) _ => do
      let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
      let m : Nat ← evalExpr Nat (mkConst ``Nat) mExpr
      return [(n, m)]
    | _ => throwSolveError "could not infer dimension of {ty}."
  | .app (.app (.app M FinN) FinM) R => do
    match (M, FinN, FinM, R) with
    | (.const ``Matrix _, .app (.const ``Fin _) nExpr, .app (.const ``Fin _) mExpr,
        .const ``Real _) =>
      let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
      let m : Nat ← evalExpr Nat (mkConst ``Nat) mExpr
      return [(n, m)]
    | _ => throwSolveError "could not infer dimension of {ty}."
  | .app (.app (.const ``Prod _) tyl) tyr => do
    let l ← inferDimension tyl
    let r ← inferDimension tyr
    return (l ++ r)
  | _ => throwSolveError "could not infer dimension of {ty}."

/-- Total dimension of a problem. For example, `ℝ × (Fin n → ℝ) × (Matrix (Fin m) (Fin k) ℝ)` has
total dimension `1 + n + mk`. We use this to know how many optimization variables to generate. -/
unsafe def getTotalDim (minExpr : MinimizationExpr) : MetaM Nat := do
  let vars ← decomposeDomainInstantiating minExpr

  let mut totalDim := 0
  for (_, varTy) in vars do
    let dims ← inferDimension varTy
    for (n, m) in dims do
      totalDim := totalDim + n * m

  return totalDim

namespace CBF

/-- Translate generic cone types from `CvxLean/Command/Solve/Float/ProblemData.lean` to MOSEK
cones. -/
def translateCone : ScalarConeType → CBF.ConeType
  | ScalarConeType.Zero => CBF.ConeType.LEq
  | ScalarConeType.PosOrth => CBF.ConeType.LPos
  | ScalarConeType.Exp => CBF.ConeType.EXP
  | ScalarConeType.Q => CBF.ConeType.Q
  | ScalarConeType.QR => CBF.ConeType.QR

/-- Constraints in non-matrix cones with intrinsic dimension (`𝒦ₑ`, `𝒬ⁿ⁺¹`, and `𝒬ᵣⁿ⁺²`) are
defined by a series of constraints. These need to be grouped appropriately. In
`CvxLean/Command/Solve/Float/Coeffs.lean` we keep track of these groups as "sections". These are
used here to correctly write the problem in CBF. -/
def groupCones (sections : ScalarAffineSections) (l : List CBF.Cone) : MetaM (List CBF.Cone) := do
  let l := l.toArray
  let mut res := []
  let mut currIdx := 0
  for idx in sections.data do
    let group := l[currIdx:idx]
    if h : group.size > 0 then
      let c := group.get ⟨0, h⟩
      let coneType := c.type
      for c' in group do
        if !(c'.type = coneType) then
          throwSolveError "only cones of the same type can be grouped."
      let totalDim := group.foldl (fun acc c => acc + c.dim) 0
      currIdx := idx
      res := res ++ [CBF.Cone.mk coneType totalDim]
    else
      throwSolveError "incorrect sections, could not group cones."

  return res

/-- Convert numerical problem data of a problem into CBF format to be solved by MOSEK. -/
unsafe def ofProblemData (minExpr : MinimizationExpr) (data : ProblemData)
    (sections : ScalarAffineSections) : MetaM CBF.Problem := do
  let totalDim ← getTotalDim minExpr

  let mut cbf := CBF.Problem.empty
  cbf := cbf.addScalarVariable (CBF.Cone.mk CBF.ConeType.F totalDim)

  if h : data.objective.isSome then
    let sa := data.objective.get h
    let AEnc := CBF.EncodedMatrixList.fromArray #[sa.A]
    let aEnc := CBF.EncodedVector.fromArray sa.a
    let bEnc := CBF.EncodedValue.mk (some sa.b)
    cbf := cbf.setObjectivePSDVariablesCoord AEnc
    cbf := cbf.setObjectiveScalarVariablesCoord aEnc
    cbf := cbf.setObjectiveShiftCoord bEnc

  for (sa, sct) in data.scalarAffineConstraints do
    let coneType := translateCone sct
    let cone := CBF.Cone.mk coneType 1
    let AEnc := CBF.EncodedMatrixList.fromArray #[sa.A]
    let aEnc := CBF.EncodedVector.fromArray sa.a
    let bEnc := sa.b
    cbf := cbf.addScalarValuedAffineConstraint cone AEnc aEnc bEnc

  for ma in data.matrixAffineConstraints do
    let HEnc := CBF.EncodedMatrixList.fromArray ma.H
    let DEnc := CBF.EncodedMatrix.fromArray ma.D
    cbf := cbf.addMatrixValuedAffineConstraint ma.n HEnc DEnc

  -- Group cones appropriately, adjusting their dimensions.
  let n := cbf.scalarConstraints.n
  let cones := cbf.scalarConstraints.cones
  let groupedCones ← groupCones sections cones
  cbf := cbf.setScalarConstraints (CBF.ConeProduct.mk n groupedCones.length groupedCones)

  return cbf

end CBF

end CvxLean
