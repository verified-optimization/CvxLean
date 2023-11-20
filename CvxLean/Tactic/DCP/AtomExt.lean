import CvxLean.Tactic.DCP.DiscrTree

namespace CvxLean

open Lean Lean.Meta

/-- An atom can be affine, concave or convex. -/
inductive Curvature where
  | Constant | Affine | Concave | Convex | AffineSet | ConvexSet
deriving BEq, Inhabited

/-- Arguments of an atom are increasing (+), decreasing (-), constant (&) or
neither (?). -/
inductive ArgKind where
  | Increasing | Decreasing | Neither | Constant
deriving BEq, Inhabited

/-- Caclulate curvature depending on monotonicity. -/
def curvatureInArg : Curvature → ArgKind → Curvature
  | _, ArgKind.Constant => Curvature.Constant
  | Curvature.Concave, ArgKind.Increasing => Curvature.Concave
  | Curvature.Concave, ArgKind.Decreasing => Curvature.Convex
  | Curvature.Convex, ArgKind.Increasing => Curvature.Convex
  | Curvature.Convex, ArgKind.Decreasing => Curvature.Concave
  | Curvature.ConvexSet, ArgKind.Increasing => Curvature.Convex
  | Curvature.ConvexSet, ArgKind.Decreasing => Curvature.Concave
  | _, _ => Curvature.Affine

instance : ToMessageData Curvature where
  toMessageData
  | Curvature.Constant => "constant"
  | Curvature.Affine => "affine"
  | Curvature.Concave => "concave"
  | Curvature.Convex => "convex"
  | Curvature.AffineSet => "affine_set"
  | Curvature.ConvexSet => "convex_set"

instance : ToMessageData ArgKind where
  toMessageData
  | ArgKind.Increasing => "increasing"
  | ArgKind.Decreasing => "decreasing"
  | ArgKind.Neither => "neither"
  | ArgKind.Constant => "constant"

section AtomData

/-- Data structure to store information about registered atoms. -/
structure GraphAtomData where
  id : Name
  curvature : Curvature
  expr : Expr
  argKinds : Array ArgKind
  bconds : Array (Lean.Name × Expr)
  vconds : Array (Lean.Name × Expr)
  impVars : Array (Lean.Name × Expr)
  impObjFun : Expr
  impConstrs : Array Expr
  solution : Array Expr
  solEqAtom: Expr
  feasibility : Array Expr
  optimality : Expr
  vcondElim : Array Expr
deriving Inhabited, BEq

instance : ToMessageData GraphAtomData where
  toMessageData d :=
    m!"safe: true
    id: {d.id}
    curvature: {d.curvature}
    expr: {d.expr}
    argKinds: {d.argKinds}
    vconds: {d.vconds}
    bconds: {d.bconds}
    impVars: {d.impVars}
    impObjFun : {d.impObjFun}
    impConstrs: {d.impConstrs}
    solution: {d.solution}
    solEqAtom: {d.solEqAtom}
    feasibility: {d.feasibility}
    optimality: {d.optimality}
    vcondElim: {d.vcondElim}"

/-- Wrapper of `GraphAtomData`. -/
inductive AtomData
  | graph (d : GraphAtomData)
deriving Inhabited, BEq

instance : ToMessageData AtomData where
  toMessageData
  | AtomData.graph d => toMessageData d

/-- Get the expression corresponding to the atom. -/
def AtomData.expr : AtomData → Expr
  | graph d => d.expr

/-- Unwrap `AtomData`. -/
def AtomData.graph! : AtomData → GraphAtomData
  | graph d => d

/-- Environment extension to store atoms. -/
def AtomExtension : Type :=
  PersistentEnvExtension
    (Array Key × AtomData) (Array Key × AtomData) (DiscrTree AtomData)
deriving Inhabited

initialize atomExtension : AtomExtension ← do
  let atomExtension ← registerPersistentEnvExtension {
    name            := `atomExtension
    mkInitial       := return {}
    addImportedFn   := fun as _ =>
      let addEntryFn :
        DiscrTree AtomData → Array Key × AtomData → DiscrTree AtomData :=
        fun s d => s.insertCore d.1 d.2
      return mkStateFromImportedEntries addEntryFn {} as,
    addEntryFn      := fun s d => s.insertCore d.1 d.2,
    exportEntriesFn := fun s => s.toArray
  }
  return atomExtension

/-- Add a new atom to the library. -/
def addAtom (data : AtomData) : MetaM Unit := do
  let (_, _, expr) ← lambdaMetaTelescope data.expr
  let keys ← DiscrTree.mkPath expr
  setEnv $ atomExtension.addEntry (← getEnv) (keys, data)

/-- Get the atom tree. -/
def getAtomDiscrTree : MetaM (DiscrTree AtomData) := do
  return atomExtension.getState (← getEnv)

end AtomData

section UnsafeAtomData

/-- Version of `GraphAtomData` where the implementation of the atom is
processed dynamically. Instead of providing a concrete implementation,
meta-level code is given, which may use the internals of the atom library.
This is useful, for instance, for higher-order atoms.

They are called unsafe because there is no assurance that they will be reduced
to conic form. The soundness of the system is not compromised as DCP is still
required to produce an equivalence. -/
structure UnsafeGraphAtomData where
  id : Name
  curvature : Curvature
  expr : Expr
  argKinds : Array ArgKind
  bconds : MetaM (Array (Lean.Name × Expr))
  vconds : MetaM (Array (Lean.Name × Expr))
  impVars : MetaM (Array (Lean.Name × Expr))
  impObjFun : MetaM Expr
  impConstrs : MetaM (Array Expr)
  solution : MetaM (Array Expr)
  solEqAtom : MetaM Expr
  feasibility : MetaM (Array Expr)
  optimality : MetaM Expr
  vcondElim : MetaM (Array Expr)
deriving Inhabited

instance : BEq UnsafeGraphAtomData where
  beq uga1 uga2 :=
    uga1.id == uga2.id &&
    uga1.curvature == uga2.curvature &&
    uga1.expr == uga2.expr &&
    uga1.argKinds == uga2.argKinds

instance : ToMessageData UnsafeGraphAtomData where
  toMessageData d :=
    m!"safe: false
    id: {d.id}
    curvature: {d.curvature}
    expr: {d.expr}
    argKinds: {d.argKinds}"

/-- Execute the meta code to get `GraphAtomData` from `UnsafeGraphAtomData`. -/
def UnsafeGraphAtomData.toGraphAtomData (uga : UnsafeGraphAtomData) :
  MetaM GraphAtomData := do
  return {
    id := uga.id,
    curvature := uga.curvature,
    expr := uga.expr,
    argKinds := uga.argKinds,
    bconds := ← uga.bconds,
    vconds := ← uga.vconds,
    impVars := ← uga.impVars,
    impObjFun := ← uga.impObjFun,
    impConstrs := ← uga.impConstrs,
    solution := ← uga.solution,
    solEqAtom := ← uga.solEqAtom,
    feasibility := ← uga.feasibility,
    optimality := ← uga.optimality,
    vcondElim := ← uga.vcondElim
  }

/-- Wrapper of `UnsafeGraphAtomData`. -/
inductive UnsafeAtomData
  | graph (d : UnsafeGraphAtomData)
deriving Inhabited, BEq

instance : ToMessageData UnsafeAtomData where
  toMessageData
  | UnsafeAtomData.graph d => toMessageData d

/-- Get the expression corresponding to the atom. -/
def UnsafeAtomData.expr : UnsafeAtomData → Expr
  | graph d => d.expr

/-- Unwrap `AtomData`. -/
def UnsafeAtomData.graph! : UnsafeAtomData → UnsafeGraphAtomData
  | graph d => d

/-- Environment extension to store atoms. -/
def UnsafeAtomExtension : Type :=
  PersistentEnvExtension
    (Array Key × UnsafeAtomData) (Array Key × UnsafeAtomData) (DiscrTree UnsafeAtomData)
deriving Inhabited

initialize unsafeAtomExtension : UnsafeAtomExtension ← do
  let atomExtension ← registerPersistentEnvExtension {
    name            := `unsafeAtomExtension
    mkInitial       := return {}
    addImportedFn   := fun as _ =>
      let addEntryFn :
        DiscrTree UnsafeAtomData → Array Key × UnsafeAtomData → DiscrTree UnsafeAtomData :=
        fun s d => s.insertCore d.1 d.2
      return mkStateFromImportedEntries addEntryFn {} as,
    addEntryFn      := fun s d => s.insertCore d.1 d.2,
    exportEntriesFn := fun s => s.toArray
  }
  return atomExtension

/-- Add a new unsafe atom to the library. -/
def addUnsafeAtom (data : UnsafeAtomData) : MetaM Unit := do
  let (_, _, expr) ← lambdaMetaTelescope data.expr
  let keys ← DiscrTree.mkPath expr
  setEnv $ unsafeAtomExtension.addEntry (← getEnv) (keys, data)

/-- Get the unsafe atoms tree. -/
def getUnsafeAtomDiscrTree : MetaM (DiscrTree UnsafeAtomData) := do
  return unsafeAtomExtension.getState (← getEnv)

end UnsafeAtomData

end CvxLean
