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

/-- Encoding the constraint ⟨X, A⟩ + ∑ i, aᵢ xᵢ + b. -/
structure ScalarAffine :=
  (n m : Nat)
  (A : Array (Array Float))
  (a : Array Float)
  (b : Float)

namespace ScalarAffine

instance : ToString ScalarAffine where
  toString sa := s!"ScalarAffine [{sa.n}, {sa.m}, {sa.A}, {sa.a}, {sa.b}]"

end ScalarAffine

/-- Encoding the constraint ∑ i, xᵢ • Hᵢ + D -/
structure MatrixAffine :=
  (n : Nat)
  (H : Array (Array (Array Float)))
  (D : Array (Array Float))

namespace MatrixAffine

instance : ToString MatrixAffine where
  toString sa :=
    s!"MatrixAffine [{sa.n}, {sa.H}, {sa.D}]"

end MatrixAffine

/-- Coeffs generates this from the problem goal. -/
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

/-- Set full objective function. -/
def setObjective (data : ProblemData)
  (A : Array (Array Float)) (a : Array Float) (b : Float)
  : ProblemData :=
  { data with objective := ScalarAffine.mk A.size a.size A a b }

/-- Same but only ∑ i, aᵢxᵢ + b. -/
def setObjectiveOnlyVector (data : ProblemData)
  (a : Array Float) (b : Float)
  : ProblemData :=
  data.setObjective #[] a b

/-- Same but only ⟨A, X⟩ + b. -/
def setObjectiveOnlyMatrix (data : ProblemData)
  (A : Array (Array Float)) (b : Float)
  : ProblemData :=
  data.setObjective A #[] b

/-- Add a full scalar affine constraint to the problem data. -/
def addScalarAffineConstraint (data : ProblemData)
  (A : Array (Array Float)) (a : Array Float) (b : Float) (sct : ScalarConeType)
  : ProblemData :=
  let constraint := ScalarAffine.mk A.size a.size A a b
  { data with scalarAffineConstraints :=
      data.scalarAffineConstraints.push ⟨constraint, sct⟩ }

/-- Add a scalar affine constraint without the ⟨A, X⟩ part. -/
def addScalarAffineConstraintOnlyVector (data : ProblemData)
  (a : Array Float) (b : Float) (sct : ScalarConeType)
  : ProblemData :=
  data.addScalarAffineConstraint #[] a b sct

/-- Specialized to the zero cone. -/
def addZeroConstraint (data : ProblemData)
  (a : Array Float) (b : Float)
  : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.Zero

/-- Specialized to the exponential cone. -/
def addExpConstraint (data : ProblemData)
  (a : Array Float) (b : Float)
  : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.Exp

/-- Specialized to the positive orthant cone. -/
def addPosOrthConstraint (data : ProblemData)
  (a : Array Float) (b : Float)
  : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.PosOrth

/- Specialized to the second-order cone. -/
def addSOConstraint (data : ProblemData)
  (a : Array Float) (b : Float)
  : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.Q

/- Specialized to the quadratic rotated cone. -/
def addRotatedSOConstraint (data : ProblemData)
  (a : Array Float) (b : Float)
  : ProblemData :=
  data.addScalarAffineConstraintOnlyVector a b ScalarConeType.QR

/-- Add a full matrix affine constraint to the problem data. -/
def addMatrixAffineConstraint (data : ProblemData)
  (H : Array (Array (Array Float))) (D : Array (Array Float))
  : ProblemData :=
  let constraint := MatrixAffine.mk D.size H D
  { data with matrixAffineConstraints :=
      data.matrixAffineConstraints.push constraint }

end ProblemData

end CvxLean
