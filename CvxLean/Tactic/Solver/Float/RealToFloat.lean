import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec
import CvxLean.Lib.Math.Data.Matrix
import CvxLean.Lib.Cones.All
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Solver.Float.Cones
import CvxLean.Tactic.Solver.Float.OptimizationParam
import CvxLean.Tactic.Solver.Float.RealToFloatExt

import CvxLean.Lib.Math.CovarianceEstimation
import CvxLean.Lib.Math.LogDet

namespace CvxLean

open Lean Lean.Elab Lean.Meta Lean.Elab.Command Lean.Elab.Term

syntax (name := addRealToFloatCommand)
  "addRealToFloat" Lean.Parser.Term.funBinder* ":" term ":=" term : command

/-- -/
partial def realToFloat (e : Expr) : MetaM Expr := do
  let e ← e.removeMData
  let discrTree ← getRealToFloatDiscrTree
  let translations ← discrTree.getMatch e
  for translation in translations do
    let (mvars, _, pattern) ← lambdaMetaTelescope translation.real
    if ← isDefEq pattern e then
    -- TODO: Search for conditions.
      let args ← mvars.mapM instantiateMVars
      return mkAppNBeta translation.float args
    else
      trace[Meta.debug] "no match: \n{pattern} \n{e}"
  -- trace[Meta.debug] "no translation found for {e}"
  match e with
  | Expr.app a b => return mkApp (← realToFloat a) (← realToFloat b)
  | Expr.lam n ty b d => return mkLambda n d (← realToFloat ty) (← realToFloat b)
  | Expr.forallE n ty b d => return mkForall n d (← realToFloat ty) (← realToFloat b)
  | Expr.mdata m e => return mkMData m (← realToFloat e)
  | Expr.letE n ty t b _ => return mkLet n (← realToFloat ty) (← realToFloat t) (← realToFloat b)
  | Expr.proj typeName idx struct => return mkProj typeName idx (← realToFloat struct)
  | e@(Expr.const n l) => do
      if ← isOptimizationParam n then
        let paramExpr ← getOptimizationParamExpr n e
        return (← realToFloat paramExpr)
      else
        return e
  | _ => return e

/- -/
def realSolutionToFloat (s : Meta.SolutionExpr) : MetaM Meta.SolutionExpr := do
  let fDomain ← realToFloat s.domain
  let fCodomain ← realToFloat s.codomain
  let fCodomainPreorder ← realToFloat s.codomainPreorder
  let fDomain' ← realToFloat s.domain'
  let fCodomain' ← realToFloat s.codomain'
  let fObjFun ← realToFloat s.objFun
  let fConstraints ← realToFloat s.constraints
  return Meta.SolutionExpr.mk fDomain fCodomain fCodomainPreorder fDomain' fCodomain' fObjFun fConstraints

@[macro addRealToFloatCommand] partial def AddRealToFloatCommand : Macro
| `(addRealToFloat $idents:funBinder* : $real := $float) => do
  if idents.size != 0 then
    return (← `(addRealToFloat : fun $idents:funBinder* => $real := fun $idents:funBinder* => $float)).raw
  else
    Macro.throwUnsupported
| _ => Macro.throwUnsupported

@[command_elab addRealToFloatCommand]
def elabAddRealToFloatCommand : CommandElab
| `(addRealToFloat : $real := $float) =>
  liftTermElabM do
    let real ← elabTermAndSynthesize real.raw none
    let float ← elabTermAndSynthesize float.raw none
    addRealToFloatData {real := real, float := float}
| _ => throwUnsupportedSyntax

syntax (name:=realToFloatCommand)
  "#realToFloat" term : command

@[command_elab realToFloatCommand]
unsafe def elabRealToFloatCommand : CommandElab
| `(#realToFloat $stx) =>
  liftTermElabM do
    let e ← elabTermAndSynthesize stx.raw none
    let res ← realToFloat e
    check res
    logInfo m!"{res}"
    if Expr.isConstOf (← inferType res) ``Float then
      let res ← Meta.evalExpr Float (mkConst ``Float) res
      logInfo m!"{res}"
| _ => throwUnsupportedSyntax


section Basic

addRealToFloat : Real :=
  Float

addRealToFloat : Real.instInhabitedReal :=
  instInhabitedFloat

addRealToFloat : Real.instZeroReal :=
  Zero.mk (0 : Float)

addRealToFloat : Real.instOneReal :=
  One.mk (1 : Float)

-- def instPreorderFloat : Preorder Float := sorry

-- addRealToFloat : Real.instPreorderReal :=
--   instPreorderFloat

addRealToFloat : Real.instLEReal :=
  instLEFloat

addRealToFloat (n : Nat) (i) : @OfNat.ofNat Real n i :=
  Float.ofNat n

addRealToFloat (n : Nat) : AddMonoidWithOne.toNatCast.natCast (R := ℝ) n :=
  Float.ofNat n

addRealToFloat (i) (x : ℕ) : @Nat.cast Real i x :=
  Float.ofNat x

addRealToFloat (n) (i1) (i2) : @instOfNat Real n i1 i2 :=
  @instOfNatFloat n

addRealToFloat (x : ℕ) (i) : @instOfNat Real x Real.natCast i :=
  @instOfNatFloat x

addRealToFloat (k : Nat) :
  @SMul.smul ℕ ℝ AddMonoid.toNatSMul k :=
  (fun (x : Float) => (OfNat.ofNat k) * x)

addRealToFloat (i) : @Ring.toNeg Real i :=
  Neg.mk Float.neg

addRealToFloat : Real.instNegReal := instNegFloat

addRealToFloat : Real.instAddReal := instAddFloat

addRealToFloat (i) : @HAdd.hAdd Real Real Real i :=
  Float.add

addRealToFloat (i) : @instHAdd Real i :=
  @HAdd.mk Float Float Float Float.add

addRealToFloat : Real.instSubReal := instSubFloat

addRealToFloat (i) : @HSub.hSub Real Real Real i :=
  Float.sub

addRealToFloat (i) : @instHSub Real i :=
  @HSub.mk Float Float Float Float.sub

addRealToFloat : Real.instMulReal := instMulFloat

addRealToFloat (i) : @HMul.hMul Real Real Real i :=
  Float.mul

addRealToFloat (i) : @instHMul Real i :=
  @HMul.mk Float Float Float Float.mul

addRealToFloat (i) (k) : @HSMul.hSMul ℕ ℝ ℝ i k :=
  fun r => Float.ofNat k * r

addRealToFloat (i) : @HDiv.hDiv Real Real Real i :=
  Float.div

addRealToFloat (i) : @instHDiv Real i :=
  @HDiv.mk Float Float Float Float.div

addRealToFloat (i) : @HPow.hPow Real Nat Real i :=
  fun f n => Float.pow f (Float.ofNat n)

addRealToFloat (i) : @HPow.hPow Real Real Real i :=
  fun f n => Float.pow f n

addRealToFloat (i) : @instHPow Real i :=
  @HPow.mk Float Float Float Float.pow

addRealToFloat (i) : @LE.le Real i :=
  Float.le

-- TODO: define Float.pi using foreign function interface
addRealToFloat : Real.pi :=
  2 * Float.acos 0

addRealToFloat : @Real.exp :=
  Float.exp

addRealToFloat : @Real.sqrt :=
  Float.sqrt

addRealToFloat : @Real.log :=
  Float.log

addRealToFloat (i) : @OfScientific.ofScientific Real i :=
  Float.ofScientific

end Basic

section Matrix

addRealToFloat (n m k) :
  @HSMul.hSMul ℕ (Matrix (Fin n) (Fin m) ℝ) (Matrix (Fin n) (Fin m) ℝ) instHSMul k :=
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

addRealToFloat (n m k : Nat) :
  @SMul.smul ℕ (Matrix (Fin n) (Fin m) ℝ) AddMonoid.toNatSMul k :=
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

addRealToFloat : @Matrix.vecEmpty Real :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Float)

addRealToFloat (n) : @Matrix.vecEmpty (Fin n → Real) :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Fin n → Float)

addRealToFloat : @Matrix.transpose.{0,0,0} :=
  @Matrix.Computable.transpose.{0,0,0}

addRealToFloat : @Matrix.diagonal.{0,0} :=
  @Matrix.Computable.diagonal.{0,0}

addRealToFloat : @Matrix.fromBlocks.{0, 0, 0, 0, 0} :=
  @Matrix.Computable.fromBlocks

addRealToFloat : @Matrix.diag.{0,0} :=
  @Matrix.Computable.diag.{0,0}

addRealToFloat (m) (i) (hm) : @Vec.sum.{0} Real i (Fin m) hm :=
  fun v => (@Matrix.Computable.vecToArray.{0} Float (Zero.mk (0 : Float)) m v).foldl (· + ·) 0

addRealToFloat (m) (i) (hm) : @Matrix.sum (Fin m) Real hm i :=
  fun M => (@Matrix.Computable.toArray Float (Zero.mk (0 : Float)) m M).foldl (fun acc v => acc + v.foldl (· + ·) 0) 0

addRealToFloat (n) (i1) (i2) (i3) : @Matrix.dotProduct (Fin n) Real i1 i2 i3 :=
  @Matrix.Computable.dotProduct Float (Zero.mk (0 : Float)) n instMulFloat instAddFloat

addRealToFloat (n m) (i1) (i2) : @Matrix.mulVec (Fin n) (Fin m) Real i1 i2 :=
  @Matrix.Computable.mulVec Float (Zero.mk (0 : Float)) n m instMulFloat instAddFloat

addRealToFloat (n m) (i1) (i2) : @Matrix.vecMul (Fin n) (Fin m) Real i1 i2 :=
  @Matrix.Computable.vecMul Float (Zero.mk (0 : Float)) n m instMulFloat instAddFloat

addRealToFloat (n : Nat) (i) :
  @Matrix.trace (Fin n) ℝ (Fin.fintype n) i :=
  @Matrix.Computable.tr Float (Zero.mk (0 : Float)) n instAddFloat

addRealToFloat (n : Nat) (i) :
  @HMul.hMul
    (Matrix (Fin n) (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ)
    i :=
  @Matrix.Computable.mul Float (Zero.mk (0 : Float)) n n n instMulFloat instAddFloat

addRealToFloat (n : Nat) (i1 i2 i3 i4) : @Matrix.PosDef (Fin n) ℝ i1 i2 i3 i4 :=
  @Matrix.Computable.PosDef Float (Zero.mk (0 : Float)) n instAddFloat instMulFloat instLTFloat

addRealToFloat (n : Nat) (i1 i2 i3 i4) : @Matrix.PosSemidef (Fin n) ℝ i1 i2 i3 i4 :=
  @Matrix.Computable.PosSemidef Float (Zero.mk (0 : Float)) n instAddFloat instMulFloat instLEFloat

def Matrix.toUpperTri' [LinearOrder m] [Zero α]
  (A : Matrix m m α) : Matrix m m α :=
fun i j => if i ≤ j then A i j else 0

addRealToFloat : @Matrix.toUpperTri.{0,0} := @Matrix.toUpperTri'.{0,0}

end Matrix

section Cones

addRealToFloat : @Real.zeroCone := @Float.zeroCone

addRealToFloat : @Real.Vec.zeroCone := @Float.Vec.zeroCone

addRealToFloat : @Real.posOrthCone := @Float.posOrthCone

addRealToFloat : @Real.Vec.posOrthCone := @Float.Vec.posOrthCone

addRealToFloat : @Real.Matrix.posOrthCone := @Float.Matrix.posOrthCone

addRealToFloat : @Real.expCone := @Float.expCone

addRealToFloat : @Real.Vec.expCone := @Float.Vec.expCone

addRealToFloat (n) (i) : @Real.Matrix.PSDCone (Fin n) i := @Float.Matrix.PSDCone n

end Cones

section CovarianceEstimation

addRealToFloat (N n : ℕ) : @covarianceMatrix N n :=
  @Matrix.Computable.covarianceMatrix Float (Zero.mk (0 : Float)) ⟨Float.add⟩ ⟨Float.mul⟩ ⟨Float.div⟩ N n (@instOfNatFloat N)

end CovarianceEstimation

end CvxLean
