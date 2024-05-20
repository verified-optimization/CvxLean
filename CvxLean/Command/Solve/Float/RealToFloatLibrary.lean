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

add_real_to_float : Real :=
  Float

add_real_to_float : Real.instInhabited :=
  instInhabitedFloat

add_real_to_float : Real.instZero :=
  Zero.mk (0 : Float)

add_real_to_float : Real.instOne :=
  One.mk (1 : Float)

add_real_to_float : Real.instLE :=
  instLEFloat

add_real_to_float : Real.instLT :=
  instLTFloat

add_real_to_float : Real.instDivReal  :=
  instDivFloat

add_real_to_float : Real.instPow :=
  Pow.mk Float.pow

add_real_to_float (n : Nat) (i) : @OfNat.ofNat Real n i :=
  Float.ofNat n

add_real_to_float (n : Nat) : AddMonoidWithOne.toNatCast.natCast (R := ℝ) n :=
  Float.ofNat n

add_real_to_float (i) (x : ℕ) : @Nat.cast Real i x :=
  Float.ofNat x

add_real_to_float (k : Nat) :
  @SMul.smul ℕ ℝ AddMonoid.toNatSMul k :=
  (fun (x : Float) => (OfNat.ofNat k) * x)

add_real_to_float (i) : @Ring.toNeg Real i :=
  Neg.mk Float.neg

add_real_to_float : Real.instNeg := instNegFloat

add_real_to_float : Real.instAdd := instAddFloat

add_real_to_float (i) : @HAdd.hAdd Real Real Real i :=
  Float.add

add_real_to_float (i) : @instHAdd Real i :=
  @HAdd.mk Float Float Float Float.add

add_real_to_float : Real.instSub := instSubFloat

add_real_to_float (i) : @HSub.hSub Real Real Real i :=
  Float.sub

add_real_to_float (i) : @instHSub Real i :=
  @HSub.mk Float Float Float Float.sub

add_real_to_float : Real.instMul := instMulFloat

add_real_to_float (i) : @HMul.hMul Real Real Real i :=
  Float.mul

add_real_to_float (i) : @instHMul Real i :=
  @HMul.mk Float Float Float Float.mul

add_real_to_float (i) (k) : @HSMul.hSMul ℕ ℝ ℝ i k :=
  fun r => Float.ofNat k * r

add_real_to_float (i) : @HDiv.hDiv Real Real Real i :=
  Float.div

add_real_to_float (i) : @instHDiv Real i :=
  @HDiv.mk Float Float Float Float.div

add_real_to_float (i) : @HPow.hPow Real Nat Real i :=
  fun f n => Float.pow f (Float.ofNat n)

add_real_to_float (i) : @HPow.hPow.{0, 0, 0} Real Real Real i :=
  fun f n => Float.pow f n

add_real_to_float (β) (i) : @instHPow Real β i :=
  @HPow.mk Float Float Float Float.pow

add_real_to_float (n) (i) : @HPow.hPow (Fin n → Real) Real (Fin n → Real) i :=
  fun (x : Fin n → Float) (p : Float) (i : Fin n) => Float.pow (x i) p

add_real_to_float (n) (β) (i) : @instHPow (Fin n → Real) β i :=
  @HPow.mk (Fin n → Float) Float (Fin n → Float) (fun x p i => Float.pow (x i) p)

add_real_to_float (i) : @LE.le Real i :=
  Float.le

add_real_to_float : Real.pi :=
  2 * Float.acos 0

add_real_to_float : @Real.exp :=
  Float.exp

add_real_to_float : @Vec.exp.{0} :=
  @Vec.Computable.exp.{0}

add_real_to_float : @Real.sqrt :=
  Float.sqrt

add_real_to_float : @Real.log :=
  Float.log

add_real_to_float (n) (i) : @Norm.norm.{0} (Fin n → ℝ) i :=
  @Real.Computable.norm n

add_real_to_float (i) : @OfScientific.ofScientific Real i :=
  Float.ofScientific

add_real_to_float : Real.instNatCast :=
  NatCast.mk Float.ofNat

end Basic

section Matrix

add_real_to_float (n m k) :
    @HSMul.hSMul ℕ (Matrix (Fin n) (Fin m) ℝ) (Matrix (Fin n) (Fin m) ℝ) instHSMul k :=
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

add_real_to_float (n k i) : @HSMul.hSMul ℕ ((Fin n) → ℝ) ((Fin n) → ℝ) i k :=
  (fun (x : (Fin n) → Float) i => (OfNat.ofNat k) * (x i))

add_real_to_float (n m k : Nat) : @SMul.smul ℕ (Matrix (Fin n) (Fin m) ℝ) AddMonoid.toNatSMul k :=
  (fun (M : Matrix (Fin n) (Fin m) Float) i j => (OfNat.ofNat k) * (M i j))

add_real_to_float (n k i) : @SMul.smul ℕ ((Fin n) → ℝ) i k :=
  (fun (x : (Fin n) → Float) i => (OfNat.ofNat k) * (x i))

add_real_to_float (i1 i2 i3) : @Algebra.toSMul ℝ ℝ i1 i2 i3 :=
  SMul.mk Float.mul

add_real_to_float : @Matrix.vecEmpty Real :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Float)

add_real_to_float (n) : @Matrix.vecEmpty (Fin n → Real) :=
  fun (x : Fin 0) => ((False.elim (Nat.not_lt_zero x.1 x.2)) : Fin n → Float)

add_real_to_float : @Matrix.transpose.{0,0,0} :=
  @Matrix.Computable.transpose.{0,0,0}

add_real_to_float (n) (α) (i1) (i2) : @Matrix.diagonal.{0,0} (Fin n) α i1 i2 :=
  @Matrix.Computable.diagonal n

add_real_to_float : @Matrix.fromBlocks.{0,0,0,0,0} :=
  @Matrix.Computable.fromBlocks

add_real_to_float : @Matrix.diag.{0,0} :=
  @Matrix.Computable.diag.{0,0}

add_real_to_float (n) (i) (hn) : @Vec.sum.{0} ℝ i (Fin n) hn :=
  @Vec.Computable.sum n

add_real_to_float (n) (i) (hn) : @Matrix.sum (Fin n) Real hn i :=
  @Matrix.Computable.sum n

add_real_to_float (n) (i) : @Vec.cumsum.{0} ℝ i n :=
  @Vec.Computable.cumsum n

add_real_to_float : @Vec.norm :=
  @Vec.Computable.norm

add_real_to_float (n) (i1) (i2) (i3) : @Matrix.dotProduct (Fin n) ℝ i1 i2 i3 :=
  @Matrix.Computable.dotProduct n

add_real_to_float (n m) (i1) (i2) : @Matrix.mulVec (Fin n) (Fin m) ℝ i1 i2 :=
  @Matrix.Computable.mulVec n m

add_real_to_float (n m) (i1) (i2) : @Matrix.vecMul (Fin n) (Fin m) ℝ i1 i2 :=
  @Matrix.Computable.vecMul n m

add_real_to_float (n : Nat) (i1) (i2) : @Matrix.trace (Fin n) ℝ i1 i2 :=
  @Matrix.Computable.trace n

add_real_to_float (l m n) (i) :
    @HMul.hMul (Matrix (Fin l) (Fin m) ℝ) (Matrix (Fin m) (Fin n) ℝ) (Matrix (Fin m) (Fin n) ℝ) i :=
  @Matrix.Computable.mul l m n

add_real_to_float (n : Nat) (i1) (i2) : @Matrix.toUpperTri.{0,0} (Fin n) ℝ i1 i2 :=
  @Matrix.Computable.toUpperTri n

add_real_to_float (n) (i) : @Inv.inv (Matrix (Fin n) (Fin n) ℝ) i :=
  @Matrix.Computable.inv n

end Matrix

section CovarianceEstimation

add_real_to_float (N n : ℕ) : @covarianceMatrix N n :=
  @Matrix.Computable.covarianceMatrix N n

end CovarianceEstimation

end CvxLean
