import CvxLean.Lib.Math.Data.Fin
import CvxLean.Lib.Cones.All
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Debug
import CvxLean.Syntax.Minimization
import CvxLean.Command.Solve.Data.ProblemData
import CvxLean.Command.Solve.FloatUtil.RealToFloatLibrary

/-!
# Extract coefficients from problem to generate problem data

This file defines `determineCoeffsFromExpr`, which takes a `MinimizationExpr` and returns
`ProblemData`. This procedure is used by `CvxLean/Commands/Solve.lean` to be able to call an
external solver.

### TODO

* This is probably a big source of inefficency for the `solve` command. We should come up with a
  better way to extract the numerical values from the Lean expressions.
* A first step is to not `unrollVectors` and turn thos expressions into floats directly.
-/

namespace CvxLean

open Lean Meta Elab Tactic

/- Generate Float expression from natural number. -/
def mkFloat (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [levelZero])
    (mkConst ``Float) (mkNatLit n) (mkApp (mkConst ``instOfNatFloat) (mkNatLit n))

/- Helper function to generate (i : Fin n) as an expression. -/
def mkFinIdxExpr (i : Nat) (n : Nat) : MetaM Expr := do
  return mkApp2 (mkConst ``Fin.ofNat) (mkNatLit n.pred) (mkNatLit i)

/- Helper function to generate (i : ty) where [OfNat ty i] as an expression. -/
def mkOfNatExpr (i : Nat) (ty : Expr) : MetaM Expr := do
  let ie := mkNatLit i
  let inst ← synthInstance (mkApp2 (mkConst ``OfNat [levelZero]) ty ie)
  return mkApp3 (mkConst ``OfNat.ofNat [levelZero]) ty ie inst

/- Evaluate floating point expressions. -/
unsafe def evalFloat (e : Expr) : MetaM Float := do
  evalExpr Float (mkConst ``Float) e

/-- Generate an array of elements of a finite type -/
unsafe def elemsOfFintype (ty : Expr) : MetaM (Array Expr) := do
  match ty with
  | .app (.const ``Fin _) nExpr => do
    let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
    let mut res := #[]
    for i in [:n] do
      res := res.push (← mkFinIdxExpr i n)
    return res
  | .app (.app (.const ``Sum lvl) tyl) tyr => do
    let elemsl := (← elemsOfFintype tyl).map fun e =>
      mkAppN (mkConst ``Sum.inl lvl) #[tyl, tyr, e]
    let elemsr := (← elemsOfFintype tyr).map fun e =>
      mkAppN (mkConst ``Sum.inr lvl) #[tyl, tyr, e]
    return elemsl ++ elemsr
  | _ => throwCoeffsError "unsupported finite type ({ty})."

/- Evaluate floating point matrix expressions. -/
unsafe def evalFloatMatrix (e : Expr) : MetaM (Array (Array Float)) := do
  let (tyn, tym) ←
    match (← inferType e) with
    | .forallE _ tyn (.forallE _ tym (.const ``Float _) _) _ =>
        pure (tyn, tym)
    | .app (.app (.app (.const ``Matrix _) tyn) tym) (.const ``Float _) =>
        pure (tyn, tym)
    | _ => throwCoeffsError "not a float matrix ({e})."
  let elemsn ← elemsOfFintype tyn
  let elemsm ← elemsOfFintype tym
  let mut res := #[]
  for i in elemsn do
    let mut row := #[]
    for j in elemsm do
      let val ← evalFloat (mkApp2 e i j)
      row := row.push val
    res := res.push row
  return res

/- Create an expression that consists of an array of zeros of the given type shape. Used to evaluate
the constant term in a constraint or objective function. -/
partial def generateZerosOfShape (ty : Expr) : MetaM Expr :=
  match ty.consumeMData with
  -- 1-dimensional variables.
  | .const ``Float _ =>
      return (mkFloat 0)
  -- Vectors.
  | .forallE _ ty (.const ``Float _) _ =>
      return (mkLambda `_ BinderInfo.default ty (mkFloat 0))
  -- Matrices.
  | .app (.app (.app (.const ``Matrix _) tyn) tym)
      (.const ``Float _) => do
      return (mkLambda `_ BinderInfo.default tyn ((mkLambda `_ BinderInfo.default tym) (mkFloat 0)))
  -- Products.
  | .app (.app (.const ``Prod _) tyl) tyr => do
      let l ← generateZerosOfShape tyl
      let r ← generateZerosOfShape tyr
      return ← mkAppM ``Prod.mk #[l, r]
  | _ => throwCoeffsError "unsupported type ({ty})."

/- Create an array of expressions where each expression is an array of the given type shape with
zeros everywhere except one place. Serves as a basis and is used to evaluate the coefficients in a
constraint or objective function. Two arrays are returned, one for scalar variables and one for
matrix variables. -/
unsafe def generateBasisOfShape (ty : Expr) : MetaM (Array Expr × Array Expr) :=
  match ty.consumeMData with
  -- 1-dimensional variables.
  | .const ``Float _ =>
      return (#[], #[mkFloat 1])
  -- Vectors.
  | .forallE _ tyn (.const ``Float _) _ => do
      let mut res := #[]
      for i in ← elemsOfFintype tyn do
        let b ← withLocalDeclD `i' tyn fun i' => do
          let ite ← mkAppM ``ite #[← mkEq i' i, mkFloat 1, mkFloat 0]
          mkLambdaFVars #[i'] ite
        res := res.push b
      return (#[], res)
  -- Matrices.
  | .app (.app (.app (.const ``Matrix _) tyn) tym) (.const ``Float _)  => do
      let mut res := #[]
      let elemsn ← elemsOfFintype tyn
      for i in elemsn do
        for j in ← elemsOfFintype tym do
          let b ← withLocalDeclD `i' tyn fun i' => do
            withLocalDeclD `j' tym fun j' => do
              let ite ← mkAppM ``ite #[mkAnd (← mkEq i' i) (← mkEq j' j), mkFloat 1, mkFloat 0]
              mkLambdaFVars #[i', j'] ite
          res := res.push b

      -- TODO: For now we're treating matrices as a bunch of scalars.
      return (#[], res)
  -- Products.
  | .app (.app (.const ``Prod _) tyl) tyr => do
      let r₀ ← generateZerosOfShape tyr
      let l₀ ← generateZerosOfShape tyl

      let (sls₁, mls₁) ← generateBasisOfShape tyl
      let sls ← sls₁.mapM fun l => mkAppM ``Prod.mk #[l, r₀]
      let mls ← mls₁.mapM fun l => mkAppM ``Prod.mk #[l, r₀]

      let (srs₁, mrs₁) ← generateBasisOfShape tyr
      let srs ← srs₁.mapM fun r => mkAppM ``Prod.mk #[l₀, r]
      let mrs ← mrs₁.mapM fun r => mkAppM ``Prod.mk #[l₀, r]

      return (sls ++ srs, mls ++ mrs)
  | _ => throwCoeffsError "unsupported type ({ty})."

/- Generates list of constraints with all the vectors unrolled. -/
unsafe def unrollVectors (constraints : Expr) : MetaM (Array Expr) := do
  let mut res := #[]
  let cs ← decomposeConstraints constraints
  for (_, c) in cs do
    let c' := Expr.consumeMData c
    match c' with
    -- Vector zero cone.
    | .app (.app (.app (.const ``Real.Vec.zeroCone _) (.app (.const ``Fin _) n)) _) e =>
        let n : Nat ← evalExpr Nat (mkConst ``Nat) n
        for i in [:n] do
          let idxExpr ← mkFinIdxExpr i n
          let ei := mkApp e idxExpr
          res := res.push (← mkAppM ``Real.zeroCone #[ei])
    -- Vector nonnegative orthant cone.
    | .app (.app (.app (.const ``Real.Vec.nonnegOrthCone _) (.app (.const ``Fin _) n)) _) e =>
        let n : Nat ← evalExpr Nat (mkConst ``Nat) n
        for i in [:n] do
          let idxExpr ← mkFinIdxExpr i n
          let ei := mkApp e idxExpr
          res := res.push (← mkAppM ``Real.nonnegOrthCone #[ei])
    -- Vector exponential cone.
    | .app (.app (.app (.app (.app
      (.const ``Real.Vec.expCone _) (.app (.const ``Fin _) n)) _) a) b) c =>
        let n : Nat ← evalExpr Nat (mkConst ``Nat) n
        for i in [:n] do
          let idxExpr ← mkFinIdxExpr i n
          let ai := mkApp a idxExpr
          let bi := mkApp b idxExpr
          let ci := mkApp c idxExpr
          res := res.push (← mkAppM ``Real.expCone #[ai, bi, ci])
    -- Vector second-order cone.
    | .app (.app (.app (.app (.app (.const ``Real.Vec.soCone _)
        exprN@(.app (.const ``Fin _) _n)) (.app (.const ``Fin _) m)) finTypeN) t) X =>
        let m : Nat ← evalExpr Nat (mkConst ``Nat) m
        for i in [:m] do
          let idxExpr ← mkFinIdxExpr i m
          let ti := mkApp t idxExpr
          let Xi := mkApp X idxExpr
          res := res.push (mkAppN (mkConst ``Real.soCone) #[exprN, finTypeN, ti, Xi])
    -- Vector rotated second-order cone.
    -- Vector second-order cone.
    | .app (.app (.app (.app (.app (.app (.const ``Real.Vec.rotatedSoCone _)
        exprN@(.app (.const ``Fin _) _n)) (.app (.const ``Fin _) m)) finTypeN) v) w) X =>
        let m : Nat ← evalExpr Nat (mkConst ``Nat) m
        for i in [:m] do
          let idxExpr ← mkFinIdxExpr i m
          let vi := mkApp v idxExpr
          let wi := mkApp w idxExpr
          let Xi := mkApp X idxExpr
          res := res.push (mkAppN (mkConst ``Real.rotatedSoCone) #[exprN, finTypeN, vi, wi, Xi])
    | _ =>
        res := res.push c

  return res

/- Given an expression (scalar constraint or objective function) and a variable `p` with type
corresponding to the domain, return the coefficients and the constant term. -/
unsafe def determineScalarCoeffsAux (e : Expr) (p : Expr) (fty : Expr) :
    MetaM (Array Float × Float) := do
  -- Constant part.
  let mut constExpr := e
  let zs ← generateZerosOfShape fty
  constExpr := constExpr.replaceFVar p zs
  let const ← evalFloat constExpr
  -- Coefficients.
  let (_, scalarBasis) ← generateBasisOfShape fty
  let mut coeffs := #[]
  for one in scalarBasis do
    let mut coeff := e.replaceFVar p one
    coeffs := coeffs.push ((← evalFloat coeff) - const)
  return (coeffs, const)

/- Same as `determineScalarCoeffsAux`, but for matrix affine constraints. -/
unsafe def determineMatrixCoeffsAux (e : Expr) (p : Expr) (fty : Expr) :
    MetaM (Array (Array (Array Float)) × Array (Array Float)) := do
  -- Constant part.
  let mut constExpr := e
  let zs ← generateZerosOfShape fty
  constExpr := constExpr.replaceFVar p zs
  let const ← evalFloatMatrix constExpr
  -- Coefficients.
  let (_, scalarBasis) ← generateBasisOfShape fty
  let mut coeffs := #[]
  for one in scalarBasis do
    let coeff := e.replaceFVar p one
    let mut floatCoeff ← evalFloatMatrix coeff
    for i in [:floatCoeff.size] do
      for j in [:floatCoeff.size] do
        let adjust := (const.get! i).get! j
        let val := (floatCoeff.get! i).get! j
        floatCoeff := floatCoeff.set! i ((floatCoeff.get! i).set! j (val - adjust))
    coeffs := coeffs.push floatCoeff
  return (coeffs, const)

/-- Given a `MinimizationExpr`, representing a problem, assuming that it is in conic form, generate
a `ProblemData`. The expression is first translated to floats, then we find the coefficients of all
the affine terms involved in the cone membership constraints by plugging in the appropriate basis
vectors and matrices and computing. This function also keeps track of how the cones are split. -/
unsafe def determineCoeffsFromExpr (minExpr : MinimizationExpr) :
    MetaM (ProblemData × ScalarAffineSections) := do
  let floatDomain ← realToFloat minExpr.domain

  -- Coefficients for objective function.
  let objectiveData ← withLambdaBody minExpr.objFun fun p objFun => do
    let objFun ← realToFloat objFun
    return ← determineScalarCoeffsAux objFun p floatDomain

  let (constraintsData, sections) ←
    withLambdaBody minExpr.constraints fun p constraints => do
    let mut data : ProblemData := ProblemData.empty
    let mut sections := #[]

    -- Constraints without vectors.
    let cs ← unrollVectors constraints

    -- Coefficients for constraints.
    let mut idx := 0
    for c in cs do
      trace[CvxLean.debug] "`coeffs` going through constraint {c}."
      let mut isTrivial := false
      match Expr.consumeMData c with
      | .const ``True _ => do
          isTrivial := true
      | .app (.const ``Real.zeroCone _) e => do
          let e ← realToFloat e
          let res ← determineScalarCoeffsAux e p floatDomain
          data := data.addZeroConstraint res.1 res.2
          idx := idx + 1
      | .app (.const ``Real.nonnegOrthCone _) e => do
          let e ← realToFloat e
          let res ← determineScalarCoeffsAux e p floatDomain
          data := data.addPosOrthConstraint res.1 res.2
          idx := idx + 1
      | .app (.app (.app (.const ``Real.expCone _) a) b) c => do
          let res ← #[a, b, c].mapM fun e => do
            let e ← realToFloat e
            return ← determineScalarCoeffsAux e p floatDomain
          -- NOTE: The order here is important. In MOSEK, x and z are swapped in the definition of
          -- the EXP cone.
          data := data.addExpConstraint res[2]!.1 res[2]!.2
          data := data.addExpConstraint res[1]!.1 res[1]!.2
          data := data.addExpConstraint res[0]!.1 res[0]!.2
          idx := idx + 3
      | .app (.app (.app (.app (.app (.const ``Real.rotatedSoCone _)
          (.app (.const ``Fin _) n)) _) v) w) x => do
          let n : Nat ← evalExpr Nat (mkConst ``Nat) n
          -- TODO: This is a common issue with all vectors.
          let xis ← (Array.range n).mapM (fun i => return (mkApp x (← mkFinIdxExpr i n)))
          for e in (#[v, w] ++ xis) do
            let e ← realToFloat e
            let (ea, eb) ← determineScalarCoeffsAux e p floatDomain
            data := data.addRotatedSOConstraint ea eb
            idx := idx + 1
      | .app (.app (.app (.app (.const ``Real.soCone _)
          (.app (.const ``Fin _) n)) _) t) x => do
          let n : Nat ← evalExpr Nat (mkConst ``Nat) n
          -- TODO: This is a common issue with all vectors.
          let xis ← (Array.range n).mapM (fun i => return (mkApp x (← mkFinIdxExpr i n)))
          for e in (#[t] ++ xis) do
            let e ← realToFloat e
            let (ea, eb) ← determineScalarCoeffsAux e p floatDomain
            data := data.addSOConstraint ea eb
            idx := idx + 1
      | .app (.app (.app (.app (.app (.const ``Real.Matrix.nonnegOrthCone _)
          (.app (.const ``Fin _) m)) (.app (.const ``Fin _) n)) _) _) e => do
          let m : Nat ← evalExpr Nat (mkConst ``Nat) m
          let n : Nat ← evalExpr Nat (mkConst ``Nat) n
          for i in [:m] do
            for j in [:n] do
              let ei := mkApp e (← mkFinIdxExpr i m)
              let eij := mkApp ei (← mkFinIdxExpr j n)
              let eij ← realToFloat eij
              let res ← determineScalarCoeffsAux eij p floatDomain
              data := data.addPosOrthConstraint res.1 res.2
              idx := idx + 1
      | .app (.app (.app (.const ``Real.Matrix.PSDCone _) mty) _) e => do
          let e ← realToFloat e
          let res ← determineMatrixCoeffsAux e p floatDomain
          -- The size of the matrix can be inferred from number of coefficients.
          let m := res.2.size
          data := data.addMatrixAffineConstraint res.1 res.2
          -- Enforce symmetry.
          for i in [:m] do
            for j in [i+1:m] do
              let ei := mkApp e (← mkOfNatExpr i mty)
              let ej := mkApp e (← mkOfNatExpr j mty)
              let eij := mkApp ei (← mkOfNatExpr j mty)
              let eji := mkApp ej (← mkOfNatExpr i mty)
              let e ← mkAppM ``Sub.sub #[eij, eji]
              let e ← realToFloat e
              let (a, b) ← determineScalarCoeffsAux e p floatDomain
              data := data.addZeroConstraint a b
              idx := idx + 1
      | _ => throwCoeffsError "no match ({c})."
      -- New group, add idx.
      if !isTrivial then
        sections := sections.push idx
    return (data, sections)

  let (objectiveDataA, objectiveDataB) := objectiveData
  let pd := constraintsData.setObjectiveOnlyVector objectiveDataA objectiveDataB

  return (pd, sections)

end CvxLean
