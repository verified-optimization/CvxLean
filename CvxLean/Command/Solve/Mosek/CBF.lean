/-!
# Conic Benchmark Format

See <https://docs.mosek.com/latest/rmosek/cbf-format.html>.

The main definition is `CBF.Problem`, the rest is a series of functions to make an element of such
type.
-/

namespace CBF

/-- Objective sense. Either a maximization or minimization problem. -/
inductive ObjSense
| MAX | MIN

namespace ObjSense

instance : ToString ObjSense where
  toString
  | MAX => "MAX"
  | MIN => "MIN"

end ObjSense

/-- Cone type: free, positive orthant, negative orthant, fixpoint zero (for equality), quadratic,
quadratic rotated or exponential. The quadratic cone is called second-order in other parts of the
project. Note that this definition is independent from the cone types in
`Command/Solve/Float/ProblemData.lean`. -/
inductive ConeType
  | F | LPos | LNeg | LEq | Q | QR | EXP
deriving DecidableEq

namespace ConeType

instance : ToString ConeType where
  toString
  | F     => "F"
  | LPos  => "L+"
  | LNeg  => "L-"
  | LEq   => "L="
  | Q     => "Q"
  | QR    => "QR"
  | EXP   => "EXP"

end ConeType

/-- Cone type and dimension. -/
structure Cone where
  type : ConeType
  dim : Nat

namespace Cone

instance : ToString Cone where
  toString c := (toString c.type) ++ " " ++ (toString c.dim)

end Cone

/-- Holds the total dimension (`n`), number of cones (`k`), and a list of cones
(`[t₁, d₁], ..., [tₖ, dₖ]`). We must have that `∑dᵢ = n`. -/
structure ConeProduct where
  n : Nat
  k : Nat
  cones : List Cone

namespace ConeProduct

instance : ToString ConeProduct where
  toString cp :=
    (toString cp.n) ++ " " ++ (toString cp.k) ++ "\n" ++
    (cp.cones.foldl (fun acc c => acc ++ (toString c) ++ "\n") "")

def empty : ConeProduct := ConeProduct.mk 0 0 []

def isEmpty (cp : ConeProduct) : Prop := cp.k = 0

instance {cp} : Decidable (isEmpty cp) := Nat.decEq _ _

def addCone (cp : ConeProduct) (c : Cone) : ConeProduct :=
  ConeProduct.mk (cp.n + c.dim) (cp.k + 1) (cp.cones.concat c)

end ConeProduct

/-- Number of dimensions and list of dimensions. -/
structure DimensionList where
  n : Nat
  dimensions : List Nat

namespace DimensionList

instance : ToString DimensionList where
  toString dl :=
    (toString dl.n) ++ "\n" ++
    (dl.dimensions.foldl (fun acc d => acc ++ (toString d) ++ "\n") "")

def empty : DimensionList := DimensionList.mk 0 []

def isEmpty (dl : DimensionList) : Prop := dl.n = 0

instance {dl} : Decidable (isEmpty dl) := Nat.decEq _ _

def addDimension (dl : DimensionList) (d : Nat) : DimensionList :=
  DimensionList.mk (dl.n + 1) (dl.dimensions.concat d)

end DimensionList

/-- Simply a float. -/
structure EncodedValue where
  value : Option Float

namespace EncodedValue

instance : ToString EncodedValue where
  toString ev := match ev.value with
    | some f => toString f
    | none => ""

def empty : EncodedValue := EncodedValue.mk none

def isEmpty (ev : EncodedValue) : Prop := ev.value.isNone

instance {ev} : Decidable (isEmpty ev) := decEq _ _

end EncodedValue

/-- Represents the value  `aᵢ`. -/
structure EncodedVectorEntry where
  i : Nat
  value : Float

namespace EncodedVectorEntry

instance : ToString EncodedVectorEntry where
  toString eve := (toString eve.i) ++ " " ++ (toString eve.value)

def fromIndexAndValue (i : Nat) (v : Float) : EncodedVectorEntry :=
  EncodedVectorEntry.mk i v

end EncodedVectorEntry

/-- Represents the vector `a = (aᵢ)` where `n` entries are non-zero. -/
structure EncodedVector where
  n : Nat
  values : List EncodedVectorEntry

namespace EncodedVector

instance : ToString EncodedVector where
  toString ev :=
    (toString ev.n) ++ "\n" ++
    (ev.values.foldl (fun acc eve => acc ++ (toString eve) ++ "\n") "")

def empty : EncodedVector := EncodedVector.mk 0 []

def isEmpty (ev : EncodedVector) : Prop := ev.n = 0

instance {ev} : Decidable (isEmpty ev) := Nat.decEq _ _

def addEntry (ev : EncodedVector) (eve : EncodedVectorEntry) : EncodedVector :=
  if eve.value < 0 || eve.value > 0 then
    EncodedVector.mk (ev.n + 1) (ev.values.concat eve)
  else
    ev

def stack (ev1 ev2 : EncodedVector) : EncodedVector :=
  EncodedVector.mk (ev1.n + ev2.n) (ev1.values ++ ev2.values)

def fromIndexAndValue (i : Nat) (v : Float) : EncodedVector :=
  if v > 0 || v < 0 then
    EncodedVector.mk 1 [EncodedVectorEntry.fromIndexAndValue i v]
  else
    EncodedVector.mk 0 []

def fromArray (a : Array Float) : EncodedVector := Id.run <| do
  let mut ev := empty
  for (i, ai) in a.data.enum do
    if ai > 0 || ai < 0 then
      ev := ev.addEntry (EncodedVectorEntry.mk i ai)
  return ev

end EncodedVector

/-- Represents the vlaue `aᵢⱼ`. -/
structure EncodedMatrixEntry where
  i : Nat
  j : Nat
  value : Float

namespace EncodedMatrixEntry

instance : ToString EncodedMatrixEntry where
  toString eme :=
    (toString eme.i) ++ " " ++
    (toString eme.j) ++ " " ++
    (toString eme.value)

def fromIndexAndEncodedVectorEntry (i : Nat) (eve : EncodedVectorEntry) : EncodedMatrixEntry :=
  EncodedMatrixEntry.mk i eve.i eve.value

end EncodedMatrixEntry

/-- Represents the matrix `A = (aᵢⱼ)` where `n` entries are non-zero. -/
structure EncodedMatrix where
  n : Nat
  values : List EncodedMatrixEntry

namespace EncodedMatrix

instance : ToString EncodedMatrix where
  toString em :=
    (toString em.n) ++ "\n" ++
    (em.values.foldl (fun acc eme => acc ++ (toString eme) ++ "\n") "")

def empty : EncodedMatrix := EncodedMatrix.mk 0 []

def isEmpty (em : EncodedMatrix) : Prop := em.n = 0

instance {em} : Decidable (isEmpty em) := Nat.decEq _ _

def addEntry (em : EncodedMatrix) (eme : EncodedMatrixEntry) : EncodedMatrix :=
  if eme.value < 0 || eme.value > 0 then
    EncodedMatrix.mk (em.n + 1) (em.values.concat eme)
  else
    em

def stack (em1 em2 : EncodedMatrix) : EncodedMatrix :=
  EncodedMatrix.mk (em1.n + em2.n) (em1.values ++ em2.values)

def fromIndexAndEncodedVector (i : Nat) (ev : EncodedVector) : EncodedMatrix := Id.run <| do
  let mut em := empty
  for eve in ev.values do
    let eme := EncodedMatrixEntry.fromIndexAndEncodedVectorEntry i eve
    em := em.addEntry eme
  em

def fromArray (A : Array (Array Float)) : EncodedMatrix := Id.run <| do
  let mut em := empty
  for (i, ai) in A.data.enum do
    for (j, aij) in ai.data.enum do
      if i >= j && (aij > 0 || aij < 0) then
        em := em.addEntry (EncodedMatrixEntry.mk i j aij)
  return em

end EncodedMatrix

/-- Represents the entry `Aⱼₖ` in the ith matrix in the list. -/
structure EncodedMatrixListEntry where
  i : Nat
  j : Nat
  k : Nat
  value : Float

namespace EncodedMatrixListEntry

instance : ToString EncodedMatrixListEntry where
  toString emle :=
    (toString emle.i) ++ " " ++
    (toString emle.j) ++ " " ++
    (toString emle.k) ++ " " ++
    (toString emle.value)

def fromIndexAndEncodedMatrixEntry (i : Nat) (eme : EncodedMatrixEntry) : EncodedMatrixListEntry :=
  EncodedMatrixListEntry.mk i eme.i eme.j eme.value

end EncodedMatrixListEntry

/-- Represents `L = [A₁, ...]` where the total number of non-zero entries of all the matrices `Aᵢ`
is `n`. -/
structure EncodedMatrixList where
  n : Nat
  values : List EncodedMatrixListEntry

namespace EncodedMatrixList

instance : ToString EncodedMatrixList where
  toString eml :=
    (toString eml.n) ++ "\n" ++
    (eml.values.foldl (fun acc emle => acc ++ (toString emle) ++ "\n") "")

def empty : EncodedMatrixList := EncodedMatrixList.mk 0 []

def isEmpty (eml : EncodedMatrixList) : Prop := eml.n = 0

instance {eml} : Decidable (isEmpty eml) := Nat.decEq _ _

def addEntry (eml : EncodedMatrixList) (emle : EncodedMatrixListEntry) : EncodedMatrixList :=
  if emle.value > 0 || emle.value < 0 then
    EncodedMatrixList.mk (eml.n + 1) (eml.values.concat emle)
  else
    eml

def stack (eml1 eml2 : EncodedMatrixList) : EncodedMatrixList :=
  EncodedMatrixList.mk (eml1.n + eml2.n) (eml1.values ++ eml2.values)

def fromIndexAndEncodedMatrix (i : Nat) (em : EncodedMatrix) : EncodedMatrixList := Id.run <| do
  let mut eml := empty
  for eme in em.values do
    let emle := EncodedMatrixListEntry.fromIndexAndEncodedMatrixEntry i eme
    eml := eml.addEntry emle
  eml

def fromArray (A : Array (Array (Array Float))) : EncodedMatrixList := Id.run <| do
  let mut eml := empty
  for (i, ai) in A.data.enum do
    for (j, aij) in ai.data.enum do
      for (k, aijk) in aij.data.enum do
        if j >= k && (aijk > 0 || aijk < 0) then
          eml := eml.addEntry (EncodedMatrixListEntry.mk i j k aijk)
  return eml

end EncodedMatrixList

/-- Represents the entry `Aₖₗ` in the `j`-th matrix of the `i`-th list. -/
structure EncodedMatrixListListEntry where
  i : Nat
  j : Nat
  k : Nat
  l : Nat
  value : Float

namespace EncodedMatrixListListEntry

instance : ToString EncodedMatrixListListEntry where
  toString emlle :=
    (toString emlle.i) ++ " " ++
    (toString emlle.j) ++ " " ++
    (toString emlle.k) ++ " " ++
    (toString emlle.l) ++ " " ++
    (toString emlle.value)

def fromIndexAndEncodedMatrixList (i : Nat) (emle : EncodedMatrixListEntry) :
    EncodedMatrixListListEntry :=
  EncodedMatrixListListEntry.mk i emle.i emle.j emle.k emle.value

end EncodedMatrixListListEntry

/-- Represents `C = [L₁, ...]` where each `Lᵢ` is a list of matrices and `n` is the total number of
non-zero entries. -/
structure EncodedMatrixListList where
  n : Nat
  values : List EncodedMatrixListListEntry

namespace EncodedMatrixListList

instance : ToString EncodedMatrixListList where
  toString emll :=
    (toString emll.n) ++ "\n" ++
    (emll.values.foldl (fun acc emlle => acc ++ (toString emlle) ++ "\n") "")

def empty : EncodedMatrixListList := EncodedMatrixListList.mk 0 []

def isEmpty (emll : EncodedMatrixListList) : Prop := emll.n = 0

instance {emll} : Decidable (isEmpty emll) := Nat.decEq _ _

def addEntry (emll : EncodedMatrixListList) (emlle : EncodedMatrixListListEntry) :
    EncodedMatrixListList :=
  if emlle.value > 0 || emlle.value < 0 then
    EncodedMatrixListList.mk (emll.n + 1) (emll.values.concat emlle)
  else emll

def stack (eml1 eml2 : EncodedMatrixListList) : EncodedMatrixListList :=
  EncodedMatrixListList.mk (eml1.n + eml2.n) (eml1.values ++ eml2.values)

def fromIndexAndEncodedMatrixList (i : Nat) (eml : EncodedMatrixList) :
    EncodedMatrixListList := Id.run <| do
  let mut emll := empty
  for emle in eml.values do
    let emlle := EncodedMatrixListListEntry.fromIndexAndEncodedMatrixList i emle
    emll := emll.addEntry emlle
  emll

def fromArray (A : Array (Array (Array (Array Float)))) :
    EncodedMatrixListList := Id.run <| do
  let mut emll := empty
  for (i, ai) in A.data.enum do
    for (j, aij) in ai.data.enum do
      for (k, aijk) in aij.data.enum do
        for (l, aijkl) in aijk.data.enum do
          if k >= l && (aijkl > 0 || aijkl < 0) then
            emll := emll.addEntry (EncodedMatrixListListEntry.mk i j k l aijkl)
  return emll

end EncodedMatrixListList

/-- This is the main definition. It represents a full problem in conic benchmark format. The problem
is defined as follows:

    min/max     g^obj
      s.t.   g_i ∈ K_i for i ∈ I        --> Scalar constraints
             G_i ∈ K_i for i ∈ I^PSD    --> PSD constraints
             x_j ∈ K_j for j ∈ J        --> Scalar variables
             X_j ∈ K_j for j ∈ J^PSD    --> PSD variables
    where
        g^obj = ∑_{j ∈ J^PSD} ⟨F^obj_j, X_j⟩ + ∑_{j ∈ J} a^obj_j * x_j + b^obj
          g_i = ∑_{j ∈ J^PSD} ⟨F_ij, X_j⟩ + ∑_{j ∈ J} a_ij * x_j + b_i
          G_i = ∑_{j ∈ J} H_ij * x_j + D_i

It contains the following headers (and their counterparts):

    VER           version
    OBJSENSE      objSense                                min/max
    VAR           scalarVariables                         x_j
    PSDVAR        PSDVariables                            X_j
    CON           scalarConstraints                       g_i
    PSDCON        PSDConstraints                          G_j
    OBJFCOORD     objectivePSDVariablesCoord              F^obj
    OBJACOORD     objectiveScalarVariablesCoord           a^obj
    OBJBCOORD     objectiveShiftCoord                     b^obj
    FCOORD        scalarConstraintsPSDVariablesCoord      F
    ACOORD        scalarConstraintsScalarVariablesCoord   a
    BCOORD        scalarConstraintsShiftCoord             b
    HCOORD        PSDConstraintsScalarVariablesCoord      H
    DCOORD        PSDConstraintsShiftCoord                D -/
structure Problem where
  version : Nat
  objSense : ObjSense
  scalarVariables : ConeProduct
  PSDVariables : DimensionList
  scalarConstraints : ConeProduct
  PSDConstraints : DimensionList
  objectivePSDVariablesCoord : EncodedMatrixList
  objectiveScalarVariablesCoord : EncodedVector
  objectiveShiftCoord : EncodedValue
  scalarConstraintsPSDVariablesCoord : EncodedMatrixListList
  scalarConstraintsScalarVariablesCoord : EncodedMatrix
  scalarConstraintsShiftCoord : EncodedVector
  PSDConstraintsScalarVariablesCoord : EncodedMatrixListList
  PSDConstraintsShiftCoord : EncodedMatrixList

namespace Problem

instance : ToString Problem where
  toString p :=
    "VER \n" ++
    (toString p.version) ++ "\n\n" ++
    "OBJSENSE \n" ++
    (toString p.objSense) ++ "\n\n" ++
    (if p.scalarVariables.isEmpty then "" else
      "VAR \n" ++
      (toString p.scalarVariables) ++ "\n") ++
    (if p.PSDVariables.isEmpty then "" else
      "PSDVAR \n" ++
      (toString p.PSDVariables) ++ "\n") ++
    (if p.scalarConstraints.isEmpty then "" else
      "CON \n" ++
      (toString p.scalarConstraints) ++ "\n") ++
    (if p.PSDConstraints.isEmpty then "" else
      "PSDCON \n" ++
      (toString p.PSDConstraints) ++ "\n") ++
    (if p.objectivePSDVariablesCoord.isEmpty then "" else
      "OBJFCOORD \n" ++
      (toString p.objectivePSDVariablesCoord) ++ "\n") ++
    (if p.objectiveScalarVariablesCoord.isEmpty then "" else
      "OBJACOORD \n" ++
      (toString p.objectiveScalarVariablesCoord) ++ "\n") ++
    (if p.objectiveShiftCoord.isEmpty then "" else
      "OBJBCOORD \n" ++
      (toString p.objectiveShiftCoord) ++ "\n\n") ++
    (if p.scalarConstraintsPSDVariablesCoord.isEmpty then "" else
      "FCOORD \n" ++
      (toString p.scalarConstraintsPSDVariablesCoord) ++ "\n") ++
    (if p.scalarConstraintsScalarVariablesCoord.isEmpty then "" else
      "ACOORD \n" ++
      (toString p.scalarConstraintsScalarVariablesCoord) ++ "\n") ++
    (if p.scalarConstraintsShiftCoord.isEmpty then "" else
      "BCOORD \n" ++
      (toString p.scalarConstraintsShiftCoord) ++ "\n") ++
    (if p.PSDConstraintsScalarVariablesCoord.isEmpty then "" else
      "HCOORD \n" ++
      (toString p.PSDConstraintsScalarVariablesCoord) ++ "\n") ++
    (if p.PSDConstraintsShiftCoord.isEmpty then "" else
      "DCOORD \n" ++
      (toString p.PSDConstraintsShiftCoord) ++ "\n")

def empty : Problem := {
  version := 3,
  objSense := ObjSense.MIN,
  scalarVariables := ConeProduct.empty,
  PSDVariables := DimensionList.empty,
  scalarConstraints := ConeProduct.empty,
  PSDConstraints := DimensionList.empty,
  objectivePSDVariablesCoord := EncodedMatrixList.empty,
  objectiveScalarVariablesCoord := EncodedVector.empty,
  objectiveShiftCoord := EncodedValue.empty,
  scalarConstraintsPSDVariablesCoord := EncodedMatrixListList.empty,
  scalarConstraintsScalarVariablesCoord := EncodedMatrix.empty,
  scalarConstraintsShiftCoord := EncodedVector.empty,
  PSDConstraintsScalarVariablesCoord := EncodedMatrixListList.empty,
  PSDConstraintsShiftCoord := EncodedMatrixList.empty
}

/- Setters. -/

def setVersion (p : Problem) (v : Nat) : Problem :=
  { p with version := v }

def setObjSense (p : Problem) (os : ObjSense) : Problem :=
  { p with objSense := os }

def setScalarVariables (p : Problem) (cp : ConeProduct) : Problem :=
  { p with scalarVariables := cp }

def setPSDVariables (p : Problem) (dl : DimensionList) : Problem :=
  { p with PSDVariables := dl }

def setScalarConstraints (p : Problem) (cp : ConeProduct) : Problem :=
  { p with scalarConstraints := cp }

def setPSDConstraints (p : Problem) (dl : DimensionList) : Problem :=
  { p with PSDConstraints := dl }

def setObjectivePSDVariablesCoord (p : Problem) (eml : EncodedMatrixList) : Problem :=
  { p with objectivePSDVariablesCoord := eml }

def setObjectiveScalarVariablesCoord (p : Problem) (ev : EncodedVector) : Problem :=
  { p with objectiveScalarVariablesCoord := ev }

def setObjectiveShiftCoord (p : Problem) (ev : EncodedValue) : Problem :=
  { p with objectiveShiftCoord := ev }

def setScalarConstraintsPSDVariablesCoord (p : Problem) (emll : EncodedMatrixListList) : Problem :=
  { p with scalarConstraintsPSDVariablesCoord := emll }

def setScalarConstraintsScalarVariablesCoord (p : Problem) (em : EncodedMatrix) : Problem :=
  { p with scalarConstraintsScalarVariablesCoord := em }

def setScalarConstraintsShiftCoord (p : Problem) (ev : EncodedVector) : Problem :=
  { p with scalarConstraintsShiftCoord := ev }

def setPSDConstraintsScalarVariablesCoord (p : Problem) (emll : EncodedMatrixListList) : Problem :=
  { p with PSDConstraintsScalarVariablesCoord := emll }

def setPSDConstraintsShiftCoord (p : Problem) (eml : EncodedMatrixList) : Problem :=
  { p with PSDConstraintsShiftCoord := eml }

/- Simple adders. -/

def addScalarVariable (p : Problem) (c : Cone) : Problem :=
  { p with scalarVariables := p.scalarVariables.addCone c }

def addPSDVariable (p : Problem) (d : Nat) : Problem :=
  { p with PSDVariables := p.PSDVariables.addDimension d }

def addScalarConstraint (p : Problem) (c : Cone) : Problem :=
  { p with scalarConstraints := p.scalarConstraints.addCone c }

def addPSDConstraint (p : Problem) (d : Nat) : Problem :=
  { p with PSDConstraints := p.PSDConstraints.addDimension d }

/- Stack adders. -/

def addScalarConstraintsPSDVariablesCoord (p : Problem) (i : Nat) (eml : EncodedMatrixList) :
    Problem :=
  let emll := EncodedMatrixListList.fromIndexAndEncodedMatrixList i eml
  { p with scalarConstraintsPSDVariablesCoord :=
      p.scalarConstraintsPSDVariablesCoord.stack emll }

def addScalarConstraintsScalarVariablesCoord (p : Problem) (i : Nat) (ev : EncodedVector) :
    Problem :=
  let em := EncodedMatrix.fromIndexAndEncodedVector i ev
  { p with scalarConstraintsScalarVariablesCoord :=
      p.scalarConstraintsScalarVariablesCoord.stack em }

def addScalarConstraintsShiftCoord (p : Problem) (i : Nat) (v : Float) : Problem :=
  let ev := EncodedVector.fromIndexAndValue i v
  { p with scalarConstraintsShiftCoord :=
      p.scalarConstraintsShiftCoord.stack ev}

def addPSDConstraintsScalarVariablesCoord
  (p : Problem) (i : Nat) (eml : EncodedMatrixList)
  : Problem :=
  let emll := EncodedMatrixListList.fromIndexAndEncodedMatrixList i eml
  { p with PSDConstraintsScalarVariablesCoord :=
      p.PSDConstraintsScalarVariablesCoord.stack emll }

def addPSDConstraintsShiftCoord (p : Problem) (i : Nat) (em : EncodedMatrix) : Problem :=
  let eml := EncodedMatrixList.fromIndexAndEncodedMatrix i em
  { p with PSDConstraintsShiftCoord :=
      p.PSDConstraintsShiftCoord.stack eml }

/- Combined adders for scalar and matrix affine constraints. -/

/- Add constraint `gₖ = ∑ ⟨Fₖᵢ, Xᵢ⟩ + ∑ aₖᵢ xᵢ + bₖ ∈ 𝒦`. -/
def addScalarValuedAffineConstraint (p : Problem) (c : Cone) (Fk : EncodedMatrixList)
    (ak : EncodedVector) (bk : Float) : Problem :=
  Id.run <| do
    let k := p.scalarConstraints.k
    let mut newP := p
    newP := newP.addScalarConstraint c
    newP := newP.addScalarConstraintsPSDVariablesCoord k Fk
    newP := newP.addScalarConstraintsScalarVariablesCoord k ak
    newP := newP.addScalarConstraintsShiftCoord k bk
    newP

/- Add constraint `G_k = ∑ x_i • H_ki  + D_k ∈ 𝒮₊ⁿ`. -/
def addMatrixValuedAffineConstraint (p : Problem) (d : Nat) (Hk : EncodedMatrixList)
    (Dk : EncodedMatrix)  : Problem :=
  Id.run <| do
    let k := p.PSDConstraints.n
    let mut newP := p
    newP := newP.addPSDConstraint d
    newP := newP.addPSDConstraintsScalarVariablesCoord k Hk
    newP := newP.addPSDConstraintsShiftCoord k Dk
    newP

end Problem

end CBF
