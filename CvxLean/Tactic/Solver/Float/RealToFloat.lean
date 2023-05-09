import CvxLean.Lib.Missing.Real
import CvxLean.Lib.Missing.Vec 
import CvxLean.Lib.Missing.Matrix 
import CvxLean.Lib.Cones
import CvxLean.Meta.Missing.Expr
import CvxLean.Meta.Minimization
import CvxLean.Tactic.Solver.Float.Cones
import CvxLean.Tactic.Solver.Float.OptimizationParam
import CvxLean.Tactic.Solver.Float.RealToFloatExt

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

-- Add to database.

addRealToFloat : Real := Float

addRealToFloat : Real.instZeroReal := Zero.mk (0 : Float)

addRealToFloat : Real.instOneReal := One.mk (1 : Float)

addRealToFloat (n : Nat) : AddMonoidWithOne.toNatCast.natCast (R := ℝ) n := 
  Float.ofNat n

addRealToFloat (i) (x : ℕ) : @Nat.cast Real i x := Float.ofNat x

addRealToFloat (n) (i1) (i2) : @instOfNat Real n i1 i2 := @instOfNatFloat n

addRealToFloat (i) : @Nat.castCoe Real i :=
  CoeT.mk Float.ofNat

addRealToFloat (x : ℕ) (i) : @instOfNat Real x Real.natCast i := 
  @instOfNatFloat x

-- #check AddMonoid 
-- -- @HSMul.hSMul ℕ (Matrix (Fin 2) (Fin 2) ℝ) (Matrix (Fin 2) (Fin 2) ℝ) instHSMul 2 X : Matrix (Fin 2) (Fin 2) ℝ
-- addRealToFloat (n m) : @Matrix.addMonoid n m Real Real.instAddMonoidReal := 
--   @Matrix.addMonoid n m Float Real.instAddMonoidReal Float.add

addRealToFloat (n m k) : 
  @HSMul.hSMul ℕ (Matrix n m ℝ) (Matrix n m ℝ) instHSMul k := 
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

addRealToFloat (n m k : Nat) : 
  @SMul.smul ℕ (Matrix (Fin n) (Fin m) ℝ) AddMonoid.SMul k := 
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

addRealToFloat (k : Nat) : 
  @SMul.smul ℕ ℝ AddMonoid.SMul k := 
  (fun (x : Float) => (OfNat.ofNat k) * x)

addRealToFloat (i) : @HAdd.hAdd Real Real Real i := Float.add 

addRealToFloat (i) : @instHAdd Real i := @HAdd.mk Float Float Float Float.add

addRealToFloat (i) : @HSub.hSub Real Real Real i := Float.sub 

addRealToFloat (i) : @instHSub Real i := @HSub.mk Float Float Float Float.sub

addRealToFloat (i) : @HMul.hMul Real Real Real i := Float.mul 

addRealToFloat (i) : @instHMul Real i := @HMul.mk Float Float Float Float.mul

addRealToFloat (i) : @HDiv.hDiv Real Real Real i := Float.div 

addRealToFloat (i) : @instHDiv Real i := @HDiv.mk Float Float Float Float.div

addRealToFloat (i) : @HPow.hPow Real Nat Real i := 
  fun f n => Float.pow f (Float.ofNat n)

addRealToFloat : @Real.exp := Float.exp

-- TODO: define Float.pi using foreign function interface
addRealToFloat : Real.pi := 2 * Float.acos 0

addRealToFloat : @Real.sqrt := Float.sqrt

addRealToFloat : @Real.log := Float.log

addRealToFloat : @Real.hasLe := @instLEFloat

def Fin.cons {α : Type} {n : Nat} (a : α) (x : Fin n → α) : Fin n.succ → α
| ⟨0, _⟩ => a
| ⟨k + 1, h⟩ => x ⟨k, Nat.lt_of_succ_lt_succ h⟩

addRealToFloat : @Matrix.vecCons := @Fin.cons

addRealToFloat : @Fin.decidableEq := @instDecidableEqFin

addRealToFloat : @Matrix.vecEmpty Real := 
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Float)

addRealToFloat (n) : @Matrix.vecEmpty (Fin n → Real) :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Fin n → Float)

-- TODO: Recover optlib
-- addRealToFloat (N n : ℕ) : @covarianceMatrix N n :=
--   @Matrix.Computable.covarianceMatrix Float (Zero.mk (0 : Float)) ⟨Float.add⟩ ⟨Float.mul⟩ ⟨Float.div⟩ N n (@instOfNatFloat N)

addRealToFloat : @Matrix.transpose.{0,0,0} := @Matrix.Computable.transpose.{0,0,0}

addRealToFloat : @Matrix.transpose.{0,0,0} := @Matrix.Computable.transpose.{0,0,0}

addRealToFloat : @Matrix.diagonal.{0,0} := @Matrix.Computable.diagonal.{0,0} 

addRealToFloat : @Matrix.fromBlocks := @Matrix.Computable.fromBlocks

addRealToFloat : @Matrix.diag.{0,0} := @Matrix.Computable.diag.{0,0}

-- Also add these, to transform the whole problem.

addRealToFloat : Nat.hasLt := instLTNat

addRealToFloat (n : Nat) : @Fin.hasZero n := Zero.mk (0 : Fin n.succ)

addRealToFloat (n : Nat) : @Fin.hasOne n := One.mk (1 : Fin n.succ)

addRealToFloat : @OfScientific.ofScientific Real Real.instOfScientificReal := 
  Float.ofScientific

addRealToFloat : Real.instOfScientificReal := instOfScientificFloat

addRealToFloat : Real.inhabited := instInhabitedFloat

addRealToFloat (m) (i) (hm) : @Vec.sum Real i (Fin m) hm := 
  fun v => (@Matrix.Computable.vecToArray Float (Zero.mk (0 : Float)) m v).foldl (· + ·) 0

addRealToFloat (m) (i) (hm) : @Matrix.sum Real (Fin m) hm i := 
  fun M => (@Matrix.Computable.toArray Float (Zero.mk (0 : Float)) m M).foldl (fun acc v => acc + v.foldl (· + ·) 0) 0

addRealToFloat (n : Nat) : @Subtype.val Nat (fun i => i < n) := @Fin.val n

addRealToFloat (n) (i1) (i2) (i3) : @Matrix.dotProduct (Fin n) Real i1 i2 i3 := 
  @Matrix.Computable.dotProduct Float (Zero.mk (0 : Float)) n instMulFloat instAddFloat

addRealToFloat (n m) (i1) (i2) : @Matrix.mulVec (Fin n) (Fin m) Real i1 i2 := 
  @Matrix.Computable.mulVec Float (Zero.mk (0 : Float)) n m instMulFloat instAddFloat

addRealToFloat (n m) (i1) (i2) : @Matrix.vecMul (Fin n) (Fin m) Real i1 i2 := 
  @Matrix.Computable.vecMul Float (Zero.mk (0 : Float)) n m instMulFloat instAddFloat

-- addRealToFloat (n : Nat) : @Matrix.PosDef ℝ Real.isROrC (Fin n) (Fin.fintype n) := 
--   @Matrix.Computable.PosDef Float (Zero.mk (0 : Float)) n instAddFloat instMulFloat instLTFloat

-- addRealToFloat (n : Nat) : @Matrix.PosSemidef ℝ Real.isROrC (Fin n) (Fin.fintype n) := 
--   @Matrix.Computable.PosSemidef Float (Zero.mk (0 : Float)) n instAddFloat instMulFloat instLEFloat

addRealToFloat (n : Nat) : 
  @Matrix.trace (Fin n) ℝ (Fin.fintype n) Real.addCommMonoid := 
  @Matrix.Computable.tr Float (Zero.mk (0 : Float)) n instAddFloat

addRealToFloat (n : Nat) : 
  @Matrix.mul (Fin n) (Fin n) (Fin n) ℝ (Fin.fintype n) Real.hasMul Real.addCommMonoid := 
  @Matrix.Computable.mul Float (Zero.mk (0 : Float)) n n n instMulFloat instAddFloat

-- Cones.

addRealToFloat : @Real.zeroCone := @Float.zeroCone

addRealToFloat : @Real.Vec.zeroCone := @Float.Vec.zeroCone

addRealToFloat : @Real.posOrthCone := @Float.posOrthCone

addRealToFloat : @Real.Vec.posOrthCone := @Float.Vec.posOrthCone

addRealToFloat : @Real.expCone := @Float.expCone

addRealToFloat : @Real.Vec.expCone := @Float.Vec.expCone

addRealToFloat : @Real.Matrix.PSDCone := @Float.Matrix.PSDCone

end CvxLean
