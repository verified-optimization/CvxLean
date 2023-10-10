import CvxLean.Syntax.Minimization
import CvxLean.Lib.Cones
import CvxLean.Tactic.Solver.Float.ProblemData
import CvxLean.Tactic.Solver.Float.RealToFloat

namespace CvxLean

open Lean
open Lean.Meta
open Meta
open Lean.Elab
open Lean.Elab.Tactic

/- Generate Float expression from natural number. 
TODO: Duplicate? Move? -/
def mkFloat (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat ([levelZero] : List Level)) 
    (mkConst ``Float) (mkNatLit n) (mkApp (mkConst ``instOfNatFloat) (mkNatLit n))

/- Helper function to generate (i : Fin n) as an expression. -/
def mkFinIdxExpr (i : Nat) (n : Nat) : MetaM Expr := do
  return mkApp2 (mkConst ``Fin.ofNat) (mkNatLit n.pred) (mkNatLit i) 

/- Evaluate floating point expressions. -/
unsafe def evalFloat (e : Expr) : MetaM Float := do
  check e
  evalExpr Float (mkConst ``Float) e

/-- Generate an array of elements of a finite type -/
unsafe def elemsOfFintype (ty : Expr) : MetaM (Array Expr) := do
  match ty with
  | Expr.app (Expr.const ``Fin _) nExpr => do
    let n : Nat ← evalExpr Nat (mkConst ``Nat) nExpr
    let mut res := #[]
    for i in [:n] do
      res := res.push (← mkFinIdxExpr i n)
    return res
  | Expr.app (Expr.app (Expr.const ``Sum lvl) tyl) tyr => do
    let elemsl := (← elemsOfFintype tyl).map fun e =>
      mkAppN (mkConst ``Sum.inl lvl) #[tyl, tyr, e]
    let elemsr := (← elemsOfFintype tyr).map fun e =>
      mkAppN (mkConst ``Sum.inr lvl) #[tyl, tyr, e]
    return elemsl ++ elemsr
  | _ => throwError "Unsupported finite type: {ty}"

/- Evaluate floating point matrix expressions. -/
unsafe def evalFloatMatrix (e : Expr) : MetaM (Array (Array Float)) := do
  let (tyn, tym) ← do (match (← inferType e) with 
  | Expr.forallE _ tyn
      (Expr.forallE _ tym
        (Expr.const ``Float _) _) _ =>
      return (tyn, tym)
  | Expr.app (Expr.app (Expr.app (Expr.const ``Matrix _) 
      tyn) tym) 
      (Expr.const ``Float _) => 
      return (tyn, tym)
  | _ => throwError "Not a float matrix: {e} {e.ctorName}.")
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

/- Create an expression that consists of an array of zeros of the given type 
shape. Used to evaluate the constant term in a constraint or objective function. 
-/
partial def generateZerosOfShape (ty : Expr) : MetaM Expr :=
  match ty.consumeMData with
  -- 1-dimensional variables.
  | Expr.const ``Float _ => 
      return (mkFloat 0)
  -- Vectors.
  | Expr.forallE _ ty (Expr.const ``Float _) _ => 
      return (mkLambda `_ Lean.BinderInfo.default ty (mkFloat 0))
  -- Matrices.
  | Expr.app (Expr.app (Expr.app (Expr.const ``Matrix _) tyn) tym)
      (Expr.const ``Float _) => do 
      return (mkLambda `_ Lean.BinderInfo.default tyn 
        ((mkLambda `_ Lean.BinderInfo.default tym) (mkFloat 0)))
  -- Products.
  | Expr.app (Expr.app (Expr.const ``Prod _) tyl) tyr => do
      let l ← generateZerosOfShape tyl
      let r ← generateZerosOfShape tyr
      return ← mkAppM ``Prod.mk #[l, r]
  | _ => throwError "Unsupported type: {ty}"

/- Create an array of expressions where each expression is an array of the given 
type shape with zeros everywhere except one place. Serves as a basis and is used
to evaluate the coefficients in a constraint or objective function. Two arrays
are returned, one for scalar variables and one for matrix variables. -/
unsafe def generateBasisOfShape (ty : Expr)
  : MetaM (Array Expr × Array Expr) :=
  match ty.consumeMData with
  -- 1-dimensional variables.
  | Expr.const ``Float _ => 
      return (#[], #[mkFloat 1])
  -- Vectors.
  | Expr.forallE _ 
      tyn
      (Expr.const ``Float _) _ => do
      let mut res := #[]
      for i in ← elemsOfFintype tyn do
        let b ← withLocalDeclD `i' tyn fun i' => do
          let ite ← mkAppM ``ite 
            #[← mkEq i' i, mkFloat 1, mkFloat 0]
          return ← mkLambdaFVars #[i'] $ ite
        res := res.push b
      return (#[], res)
  -- Matrices.
  | Expr.app (Expr.app (Expr.app (Expr.const ``Matrix _) tyn)  tym) 
      (Expr.const ``Float _)  => do
      let mut res := #[]
      let elemsn ← elemsOfFintype tyn
      for i in elemsn do
        for j in ← elemsOfFintype tym do 
          let b ← withLocalDeclD `i' tyn fun i' => do
            withLocalDeclD `j' tym fun j' => do
              let ite ← mkAppM ``ite 
                #[mkAnd (← mkEq i' i) (← mkEq j' j), 
                  mkFloat 1, mkFloat 0]
              return ← mkLambdaFVars #[i', j'] $ ite
          res := res.push b
      -- TODO: For now we're treating matrices as a bunch of scalars.
      return (#[], res)
  -- Products.
  | Expr.app (Expr.app (Expr.const ``Prod _) tyl) tyr => do
      let r₀ ← generateZerosOfShape tyr
      let l₀ ← generateZerosOfShape tyl
      
      -- TODO: This might be wrong. We want all the basis together but identify 
      -- when we put ones on the matrices.
      let (sls₁, mls₁) ← generateBasisOfShape tyl
      let sls ← sls₁.mapM fun l => mkAppM ``Prod.mk #[l, r₀]
      let mls ← mls₁.mapM fun l => mkAppM ``Prod.mk #[l, r₀]
      
      let (srs₁, mrs₁) ← generateBasisOfShape tyr
      let srs ← srs₁.mapM fun r => mkAppM ``Prod.mk #[l₀, r]
      let mrs ← mrs₁.mapM fun r => mkAppM ``Prod.mk #[l₀, r]
      
      return (sls ++ srs, mls ++ mrs)
  | _ => throwError "Unsupported type: {ty}"

/- Generates list of constraints with all the vectors unrolled. -/
unsafe def unrollVectors (constraints : Expr) : MetaM (Array Expr) := do 
  let mut res := #[]
  let cs ← decomposeConstraints constraints
  for (_, c) in cs do
    let c' := Expr.consumeMData c
    match c' with
    -- Vector zero cone. 
    | Expr.app (Expr.app (Expr.const ``Real.Vec.zeroCone _) n) e =>
        let n : Nat ← evalExpr Nat (mkConst ``Nat) n
        for i in [:n] do 
          let idxExpr ← mkFinIdxExpr i n
          let ei := mkApp e idxExpr
          res := res.push (← mkAppM ``Real.zeroCone #[ei]) 
    -- Positive orthant cone.
    | Expr.app (Expr.app (Expr.const ``Real.Vec.posOrthCone _) n) e =>
        let n : Nat ← evalExpr Nat (mkConst ``Nat) n
        for i in [:n] do 
          let idxExpr ← mkFinIdxExpr i n
          let ei := mkApp e idxExpr
          res := res.push (← mkAppM ``Real.posOrthCone #[ei]) 
    -- Vector exponential cone.
    | Expr.app (Expr.app (Expr.app (Expr.app 
        (Expr.const ``Real.Vec.expCone _) n) a) b) c => 
        let n : Nat ← evalExpr Nat (mkConst ``Nat) n 
        for i in [:n] do 
          let idxExpr ← mkFinIdxExpr i n
          let ai := mkApp a idxExpr
          let bi := mkApp b idxExpr
          let ci := mkApp c idxExpr
          res := res.push (← mkAppM ``Real.expCone #[ai, bi, ci])
    | _ => 
        res := res.push c
  
  return res

/- Given an expression (scalar constraint or objective function) and a variable 
`p` with type corresponding to the domain, return the coefficients and the 
constant term. -/
unsafe def determineScalarCoeffsAux (e : Expr) (p : Expr) (fty : Expr)
  : MetaM (Array Float × Float) := do
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

/- Same as above, but for matrix affine constraints. -/
unsafe def determineMatrixCoeffsAux (e : Expr) (p : Expr) (fty : Expr) 
  : MetaM (Array (Array (Array Float)) × Array (Array Float)) := do 
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


unsafe def determineCoeffsFromExpr (goalExprs : Meta.SolutionExpr) 
  : MetaM ProblemData := do
  let floatDomain ← realToFloat goalExprs.domain

  -- Coefficients for objective function.
  let objectiveData ← withLambdaBody goalExprs.objFun fun p objFun => do 
    let objFun ← realToFloat objFun
    return ← determineScalarCoeffsAux objFun p floatDomain 

  let constraintsData ← withLambdaBody goalExprs.constraints fun p constraints => do
    let mut data : ProblemData := ProblemData.empty
  
    -- Constraints without vectors.
    let cs ← unrollVectors constraints

    -- Coefficients for constraints.
    for c in cs do
      trace[Meta.debug] "Coeffs going through constraint {c}."
      match Expr.consumeMData c with
      | Expr.app (Expr.const ``Real.zeroCone _) e => do 
          let e ← realToFloat e
          let res ← determineScalarCoeffsAux e p floatDomain
          data := data.addZeroConstraint res.1 res.2 
      | Expr.app (Expr.const ``Real.posOrthCone _) e => do 
          let e ← realToFloat e
          let res ← determineScalarCoeffsAux e p floatDomain
          data := data.addPosOrthConstraint res.1 res.2 
      | Expr.app (Expr.app (Expr.app (Expr.const ``Real.expCone _) a) b) c => do
          let res ← #[a, b, c].mapM fun e => do
            let e ← realToFloat e
            return ← determineScalarCoeffsAux e p floatDomain
          -- Note: The order here is important. In MOSEK, x and z are swapped in 
          -- the definition of the EXP cone.
          data := data.addExpConstraint res[2]!.1 res[2]!.2
          data := data.addExpConstraint res[1]!.1 res[1]!.2
          data := data.addExpConstraint res[0]!.1 res[0]!.2
      | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app 
          (Expr.const ``Real.rotatedSoCone _) 
          (Expr.app (Expr.const ``Fin _) n)) _) v) w) x => do 
          let n : Nat ← evalExpr Nat (mkConst ``Nat) n 
          -- TODO: This is a common issue with all vectors.
          let xis ← (Array.range n).mapM 
            (fun i => return (mkApp x (← mkFinIdxExpr i n)))
          for e in (#[v, w] ++ xis) do
            let e ← realToFloat e
            let (ea, eb) ← determineScalarCoeffsAux e p floatDomain
            data := data.addRotatedSOConstraint ea eb
      | Expr.app (Expr.app (Expr.app (Expr.const ``Real.Matrix.posOrthCone _) m) n) e => do 
          let m : Nat ← evalExpr Nat (mkConst ``Nat) m
          let n : Nat ← evalExpr Nat (mkConst ``Nat) n  
          for i in [:m] do 
            for j in [:n] do 
              let ei := mkApp e (← mkFinIdxExpr i m)
              let eij := mkApp ei (← mkFinIdxExpr j n)
              let eij ← realToFloat eij
              let res ← determineScalarCoeffsAux eij p floatDomain
              data := data.addPosOrthConstraint res.1 res.2 
      | Expr.app (Expr.app (Expr.app (Expr.const ``Real.Matrix.PSDCone _) m) mi) e => do 
          trace[Meta.debug] "PSD constraint 1 {e}"
          let e ← realToFloat e 
          trace[Meta.debug] "PSD constraint 2 {e}"
          let res ← determineMatrixCoeffsAux e p floatDomain 
          trace[Meta.debug] "PSD constraint 3 {res}"
          data := data.addMatrixAffineConstraint res.1 res.2
      | _ => throwError "No match: {c}."
    return data
  
  return constraintsData.setObjectiveOnlyVector objectiveData.1 objectiveData.2

/-- Generate problem data from goal. -/
unsafe def determineCoeffs (goal : Lean.MVarId) : MetaM ProblemData := do
  let goalExprs ← Meta.SolutionExpr.fromGoal goal
  
  determineCoeffsFromExpr goalExprs

namespace  Tactic

open Lean.Elab
open Lean.Elab.Tactic

syntax (name := coeffs) "coeffs" : tactic

@[tactic coeffs]
unsafe def evalCoeffs : Tactic := fun stx => match stx with
| `(tactic| coeffs) => do
  let data ← determineCoeffs (← getMainGoal)
  logInfo m!"PROBLEM DATA \n {data}."
| _ => throwUnsupportedSyntax

end Tactic

end CvxLean
