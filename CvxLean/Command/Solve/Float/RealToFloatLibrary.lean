import CvxLean.Command.Solve.Float.RealToFloatCmd

/-!
# Conversion of Real to Float (library)

We define all the specific real-to-float translations here. Any issues with real-to-float are
likely due to missing translations. Users need to make sure that the types of the translations
correspond to the required types. For example, an expression of type `ℝ` needs to map to an
expression of type `Float`, and an expression of type `Fin n → ℝ → ℝ` needs to map to an expression
of type `Fin n → Float → Float`.
-/

namespace CvxLean

section Basic

addRealToFloat : Real :=
  Float

addRealToFloat : Real.instInhabitedReal :=
  instInhabitedFloat

addRealToFloat : Real.instZeroReal :=
  Zero.mk (0 : Float)

addRealToFloat : Real.instOneReal :=
  One.mk (1 : Float)

addRealToFloat : Real.instLEReal :=
  instLEFloat

addRealToFloat : Real.instLTReal :=
  instLTFloat

addRealToFloat : Real.instDivReal  :=
  instDivFloat

addRealToFloat : Real.instPowReal :=
  Pow.mk Float.pow

addRealToFloat (n : Nat) (i) : @OfNat.ofNat Real n i :=
  Float.ofNat n

addRealToFloat (n : Nat) : AddMonoidWithOne.toNatCast.natCast (R := ℝ) n :=
  Float.ofNat n

addRealToFloat (i) (x : ℕ) : @Nat.cast Real i x :=
  Float.ofNat x

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

addRealToFloat (i) : @HPow.hPow.{0, 0, 0} Real Real Real i :=
  fun f n => Float.pow f n

addRealToFloat (β) (i) : @instHPow Real β i :=
  @HPow.mk Float Float Float Float.pow

addRealToFloat (n) (i) : @HPow.hPow (Fin n → Real) Real (Fin n → Real) i :=
  fun (x : Fin n → Float) (p : Float) (i : Fin n) => Float.pow (x i) p

addRealToFloat (n) (β) (i) : @instHPow (Fin n → Real) β i :=
  @HPow.mk (Fin n → Float) Float (Fin n → Float) (fun x p i => Float.pow (x i) p)

addRealToFloat (i) : @LE.le Real i :=
  Float.le

addRealToFloat : Real.pi :=
  2 * Float.acos 0

addRealToFloat : @Real.exp :=
  Float.exp

addRealToFloat : @Vec.exp.{0} :=
  @Vec.Computable.exp.{0}

addRealToFloat : @Real.sqrt :=
  Float.sqrt

addRealToFloat : @Real.log :=
  Float.log

addRealToFloat (n) (i) : @Norm.norm.{0} (Fin n → ℝ) i :=
  @Real.Computable.norm n

addRealToFloat (i) : @OfScientific.ofScientific Real i :=
  Float.ofScientific

addRealToFloat : Real.natCast :=
  NatCast.mk Float.ofNat

end Basic

section Matrix

addRealToFloat (n m k) :
    @HSMul.hSMul ℕ (Matrix (Fin n) (Fin m) ℝ) (Matrix (Fin n) (Fin m) ℝ) instHSMul k :=
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

addRealToFloat (n k i) : @HSMul.hSMul ℕ ((Fin n) → ℝ) ((Fin n) → ℝ) i k :=
  (fun (x : (Fin n) → Float) i => (OfNat.ofNat k) * (x i))

addRealToFloat (n m k : Nat) : @SMul.smul ℕ (Matrix (Fin n) (Fin m) ℝ) AddMonoid.toNatSMul k :=
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

addRealToFloat (n k i) : @SMul.smul ℕ ((Fin n) → ℝ) i k :=
  (fun (x : (Fin n) → Float) i => (OfNat.ofNat k) * (x i))

addRealToFloat (i1 i2 i3) : @Algebra.toSMul ℝ ℝ i1 i2 i3 :=
  SMul.mk Float.mul

addRealToFloat : @Matrix.vecEmpty Real :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Float)

addRealToFloat (n) : @Matrix.vecEmpty (Fin n → Real) :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Fin n → Float)

addRealToFloat : @Matrix.transpose.{0,0,0} :=
  @Matrix.Computable.transpose.{0,0,0}

addRealToFloat (n) (α) (i1) (i2) : @Matrix.diagonal.{0,0} (Fin n) α i1 i2 :=
  @Matrix.Computable.diagonal n

addRealToFloat : @Matrix.fromBlocks.{0,0,0,0,0} :=
  @Matrix.Computable.fromBlocks

addRealToFloat : @Matrix.diag.{0,0} :=
  @Matrix.Computable.diag.{0,0}

addRealToFloat (n) (i) (hn) : @Vec.sum.{0} ℝ i (Fin n) hn :=
  @Vec.Computable.sum n

addRealToFloat (n) (i) (hn) : @Matrix.sum (Fin n) Real hn i :=
  @Matrix.Computable.sum n

addRealToFloat (n) (i) : @Vec.cumsum.{0} ℝ i n :=
  @Vec.Computable.cumsum n

addRealToFloat : @Vec.norm :=
  @Vec.Computable.norm

addRealToFloat (n) (i1) (i2) (i3) : @Matrix.dotProduct (Fin n) ℝ i1 i2 i3 :=
  @Matrix.Computable.dotProduct n

addRealToFloat (n m) (i1) (i2) : @Matrix.mulVec (Fin n) (Fin m) ℝ i1 i2 :=
  @Matrix.Computable.mulVec n m

addRealToFloat (n m) (i1) (i2) : @Matrix.vecMul (Fin n) (Fin m) ℝ i1 i2 :=
  @Matrix.Computable.vecMul n m

addRealToFloat (n : Nat) (i1) (i2) : @Matrix.trace (Fin n) ℝ i1 i2 :=
  @Matrix.Computable.trace n

addRealToFloat (l m n) (i) :
    @HMul.hMul (Matrix (Fin l) (Fin m) ℝ) (Matrix (Fin m) (Fin n) ℝ) (Matrix (Fin m) (Fin n) ℝ) i :=
  @Matrix.Computable.mul l m n

addRealToFloat (n : Nat) (i1) (i2) : @Matrix.toUpperTri.{0,0} (Fin n) ℝ i1 i2 :=
  @Matrix.Computable.toUpperTri n

end Matrix

section CovarianceEstimation

addRealToFloat (N n : ℕ) : @covarianceMatrix N n :=
  @Matrix.Computable.covarianceMatrix N n

end CovarianceEstimation

end CvxLean
