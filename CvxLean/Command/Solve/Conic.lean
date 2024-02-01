import CvxLean.Lib.Minimization
import CvxLean.Lib.Math.Data.Array
import CvxLean.Lib.Math.Data.Matrix
import CvxLean.Lib.Math.Data.Real
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.ToExpr
import CvxLean.Meta.Minimization
import CvxLean.Syntax.Minimization
import CvxLean.Command.Solve.Float.Coeffs
import CvxLean.Command.Solve.Float.FloatToReal
import CvxLean.Command.Solve.Mosek.Sol
import CvxLean.Command.Solve.InferDimension
import CvxLean.Command.Solve.Mosek.CBF
import CvxLean.Command.Solve.Mosek.Path

namespace CvxLean

namespace Meta

open Lean Lean.Meta Minimization

def translateCone : ScalarConeType → CBF.ConeType
  | ScalarConeType.Zero => CBF.ConeType.LEq
  | ScalarConeType.PosOrth => CBF.ConeType.LPos
  | ScalarConeType.Exp => CBF.ConeType.EXP
  | ScalarConeType.Q => CBF.ConeType.Q
  | ScalarConeType.QR => CBF.ConeType.QR

def groupCones (sections : ScalarAffineSections) (l : List CBF.Cone) :
  MetaM (List CBF.Cone) := do
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
          throwError "Only cones of the same type can be grouped."
      let totalDim := group.foldl (fun acc c => acc + c.dim) 0
      currIdx := idx
      res := res ++ [CBF.Cone.mk coneType totalDim]
    else
      throwError "Incorrect sections, could not group cones."

  return res

/-- -/
def getVars (minExpr : MinimizationExpr) : MetaM (List (Lean.Name × Expr)) := do
  decomposeDomain (← instantiateMVars minExpr.domain)

/-- -/
unsafe def getTotalDim (minExpr : MinimizationExpr) : MetaM Nat := do
  let vars ← getVars minExpr

  let mut totalDim := 0
  for (_, varTy) in vars do
    let dims ← inferDimension varTy
    for (n, m) in dims do
      totalDim := totalDim + n * m

  return totalDim

/-- -/
unsafe def conicSolverFromValues (minExpr : MinimizationExpr) (data : ProblemData)
  (sections : ScalarAffineSections) : MetaM Sol.Response := do
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
  cbf := cbf.setScalarConstraints
    (CBF.ConeProduct.mk n groupedCones.length groupedCones)

  let r ← IO.rand 0 (2 ^ 32 - 1)
  let outputPath := s!"solver/problem{r}.sol"
  let inputPath := s!"solver/problem{r}.cbf"
  IO.FS.writeFile inputPath ""
  IO.FS.writeFile outputPath ""
  IO.FS.withFile outputPath IO.FS.Mode.read fun outHandle => do
    IO.FS.withFile inputPath IO.FS.Mode.write fun inHandle => do
      -- Write input.
      inHandle.putStr (ToString.toString cbf)

      -- Adjust path to MOSEK.
      let p := if let some p' := ← IO.getEnv "PATH" then
        if mosekBinPath != "" then p' ++ ":" ++ mosekBinPath else p'
      else
        mosekBinPath

      -- Run solver.
      let out ← IO.Process.output {
        cmd := "mosek",
        args := #[inputPath],
        env := #[("PATH", p)] }

      if out.exitCode != 0 then
        dbg_trace ("MOSEK exited with code " ++ ToString.toString out.exitCode)
        return Sol.Response.failure out.exitCode.toNat

      let res := out.stdout
      IO.println res

      -- Read output.
      let output ← outHandle.readToEnd

      -- Remove temporary files.
      IO.FS.removeFile inputPath
      IO.FS.removeFile outputPath

      match Sol.Parser.parse output with
      | Except.ok res => return Sol.Response.success res
      | Except.error err =>
          dbg_trace ("MOSEK output parsing failed. " ++ err)
          return Sol.Response.failure 1

/-- TODO: Move to Generation? -/
unsafe def exprFromSol (minExpr : MinimizationExpr) (sol : Sol.Result) : MetaM Expr := do
  let vars ← getVars minExpr

  -- Generate solution of the correct shape.
  let solPointExprArrayRaw : Array Expr :=
    Array.mk <| sol.vars.map (fun v => floatToReal v.activity)

  -- Vectors and matrices as functions.
  let mut solPointExprArray : Array Expr := #[]

  -- TODO(RFM): This won't work in general, need to take into account the
  -- associativity of the variables if there are products. Infer dimension might
  -- need to return a tree.
  let mut i : ℕ := 0
  for (_, varTy) in vars do
    let dims ← inferDimension varTy
    -- NOTE: This is because a var type can be a product itself. Ignore for now.
    for (n, m) in dims do
      if n = 1 ∧ m = 1 then
        -- Basic type.
        solPointExprArray := solPointExprArray.push (solPointExprArrayRaw[i]!)
        i := i + 1
      else if n ≠ 0 ∧ m = 1 then
        -- Vector.
        let exprs := (solPointExprArrayRaw.drop i).take n

        -- TODO: Many copies of this in the function
        let arrayExpr ← Lean.Expr.mkArray (mkConst ``Real) exprs
        let arrayList ← mkAppM ``Array.toList #[arrayExpr]
        let v ← withLocalDeclD `i' (← mkAppM ``Fin #[toExpr n]) fun i' => do
          let i'' := mkApp2 (mkConst ``Fin.val) (toExpr n) i'
          -- Get from generated array.
          let r ← mkAppM ``List.get! #[arrayList, i'']
          mkLambdaFVars #[i'] r

        solPointExprArray := solPointExprArray.push v
        i := i + n
      else
        -- Matrix.
        let mut exprs := #[]
        for j in [:m] do
          let arrayExpr ← Lean.Expr.mkArray (mkConst ``Real) ((solPointExprArrayRaw.drop (i + j * n)).take n)
          let listExpr ← mkAppM ``Array.toList #[arrayExpr]
          exprs := exprs.push listExpr

        let arrayListExpr ←
          Lean.Expr.mkArray (← mkAppM ``List #[mkConst ``Real]) exprs

        -- List of list representing the matrix.
        let listListExpr ← mkAppM ``Array.toList #[arrayListExpr]

        let M ← withLocalDeclD `i' (← mkAppM ``Fin #[toExpr n]) fun i' => do
          let i'' := mkApp2 (mkConst ``Fin.val) (toExpr n) i'
          let ri ← mkAppM ``List.get! #[listListExpr, i'']
          withLocalDeclD `j' (← mkAppM ``Fin #[toExpr m]) fun j' => do
            let j'' := mkApp2 (mkConst ``Fin.val) (toExpr m) j'
            let rij ← mkAppM ``List.get! #[ri, j'']
            mkLambdaFVars #[i', j'] rij

        solPointExprArray := solPointExprArray.push M
        i := i + n * m

  let solPointExpr : Expr ← Lean.Expr.mkProd solPointExprArray

  return solPointExpr

end Meta

end CvxLean
