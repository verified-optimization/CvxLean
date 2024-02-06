/-!
# Representation of numerical problem data

This file defines an intermediate representation of a problem in conic form at the level of floats.
We provide an interface to build this data by adding any of the possible types of constraints. This
data can then be transformed in a straightforward manner into Conic Benchmark Format, for example.

The procedure that creates `ProblemData` from an optimization problem can be found in
`CvxLean/Command/Solve/Coeffs.lean`.
-/

namespace CvxLean

/-- Cones admitting scalar affine constraints. Note that the only cone that admits matrix affine
constraints is the PSD cone. -/
inductive ScalarConeType
  | Zero | PosOrth | Exp | Q | QR

namespace ScalarConeType

instance : ToString ScalarConeType where
  toString
  | Zero => "Zero"
  | PosOrth => "PosOrth"
  | Exp => "Exp"
  | Q => "Q"
  | QR => "QR"

end ScalarConeType

/-- Encodes the expression `⟨X, A⟩ + ∑ i, aᵢ xᵢ + b`. -/
structure ScalarAffine :=
  (n m : Nat)
  (A : Array (Array Float))
  (a : Array Float)
  (b : Float)

namespace ScalarAffine

instance : ToString ScalarAffine where
  toString sa := s!"ScalarAffine [{sa.n}, {sa.m}, {sa.A}, {sa.a}, {sa.b}]"

end ScalarAffine

/-- Encodies the expression `∑ i, xᵢ • Hᵢ + D`. -/
structure MatrixAffine :=
  (n : Nat)
  (H : Array (Array (Array Float)))
  (D : Array (Array Float))

namespace MatrixAffine

instance : ToString MatrixAffine where
  toString sa := s!"MatrixAffine [{sa.n}, {sa.H}, {sa.D}]"

end MatrixAffine

/-- Data structure storing the floating-point coefficient of the objective function and constraints
of a problem in conic form. -/
structure ProblemData :=
  (objective : Option ScalarAffine)
  (scalarAffineConstraints : Array (ScalarAffine × ScalarConeType))
  (matrixAffineConstraints : Array MatrixAffine)

namespace ProblemData

instance : ToString ProblemData where
  toString data :=
    let scalarConstraintsStr := data.scalarAffineConstraints.map
      (fun (sa, sct) => (toString sct) ++ " " ++ (toString sa))
    let matrixConstraintsStr := data.matrixAffineConstraints.map
      (fun ma => "PSD " ++ (toString ma))
    let constraintsStr := (scalarConstraintsStr ++ matrixConstraintsStr).map
      (fun s => "* " ++ s ++ "\n")
    "Objective: " ++ toString (data.objective) ++ "\n" ++
    "Constraints: \n" ++ String.join constraintsStr.data

def empty : ProblemData :=
  ProblemData.mk none #[] #[]

instance : Inhabited ProblemData where
  default := empty

/-- Set full objective function of the form `⟨X, A⟩ + ∑ i, aᵢ xᵢ + b`. -/
def setObjective (data : ProblemData) (A : Array (Array Float)) (a : Array Float) (b : Float) :
    ProblemData :=
  { data with objective := ScalarAffine.mk A.size a.size A a b }

/-- Same as `setObjective` if the objective is of the form `∑ i, aᵢxᵢ + b`. -/
def setObjectiveOnlyVector (data : ProblemData) (a : Array Float) (b : Float) : ProblemData :=
  data.setObjective #[] a b

/-- Same as `setObjective` if the objective is of the form `⟨A, X⟩ + b`. -/
def setObjectiveOnlyMatrix (data : ProblemData) (A : Array (Array Float)) (b : Float) :
    ProblemData :=
  data.setObjective A #[] b

/-- Add a scalar affine constraint of the form ``⟨X, A⟩ + ∑ i, aᵢ xᵢ + b ∈ 𝒦`, where `𝒦` is a cone
of type `sct`. -/
def addScalarAffineConstraint (data : ProblemData) (A : Array (Array Float)) (a : Array Float)
    (b : Float) (sct : ScalarConeType) : ProblemData :=
  let constraint := ScalarAffine.mk A.size a.size A a b
  { data with scalarAffineConstraints :=
      data.scalarAffineConstraints.push ⟨constraint, sct⟩ }

/-- Same as `addScalarAffineConstraint` if the constraint is of the form `∑ i, aᵢ xᵢ + b ∈ 𝒦`. -/
def addScalarAffineConstraintOnlyVector (data : ProblemData) (a : Array Float) (b : Float)
    (sct : ScalarConeType) : ProblemData :=
  data.addScalarAffineConstraint #[] a b sct

/-- Add zero cone constraint `∑ i, aᵢxᵢ + b ∈ 0` to problem data. -/
def addZeroConstraint (data : ProblemData) (a : Array Float) (b : Float) : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.Zero

/-- Add exponential cone constraint `∑ i, aᵢxᵢ + b ∈ 𝒦ₑ` to problem data. Note that the
second-order cone is `3`-dimensional, so to capture `(x, y, z) ∈ 𝒦ₑ` we do `x ∈ 𝒦ₑ`, `y ∈ 𝒦ₑ`, and
`z ∈ 𝒦ₑ` consecutively. We keep track of how to group consecutive constraints in
`CvxLean/Command/Solve/Float/Coeffs.lean`. -/
def addExpConstraint (data : ProblemData) (a : Array Float) (b : Float) : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.Exp

/-- Add positive orthant cone constraint `∑ i, aᵢxᵢ + b ∈ ℝ₊` to problem data. -/
def addPosOrthConstraint (data : ProblemData) (a : Array Float) (b : Float) : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.PosOrth

/-- Add second-order cone constraint `∑ i, aᵢxᵢ + b ∈ 𝒬` to problem data. Note that the second-order
cone is `n+1`-dimensional. The same remark on grouping constraints in `addExpConstraint` applies. -/
def addSOConstraint (data : ProblemData) (a : Array Float) (b : Float) : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.Q

/- Add second-order cone constraint `∑ i, aᵢxᵢ + b ∈ 𝒬ᵣ` to problem data. Note that the rotated
second-order cone is `n+2`-dimensional. The same remark on grouping constraints in
`addExpConstraint` applies. -/
def addRotatedSOConstraint (data : ProblemData) (a : Array Float) (b : Float) : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.QR

/-- Add a matrix affine constraint `∑ i, xᵢ • Hᵢ + D ∈ 𝒮₊ⁿ` to problem data. The only matrix cone
we consider is the PSD cone. -/
def addMatrixAffineConstraint (data : ProblemData) (H : Array (Array (Array Float)))
    (D : Array (Array Float)) : ProblemData :=
  let constraint := MatrixAffine.mk D.size H D
  { data with matrixAffineConstraints := data.matrixAffineConstraints.push constraint }

end ProblemData

/-- Indices to group constraints together and tag cones with the correct dimension when translating
problem data to solver formats. -/
def ScalarAffineSections : Type := Array Nat

end CvxLean
