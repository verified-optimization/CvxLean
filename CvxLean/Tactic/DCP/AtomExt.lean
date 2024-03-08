import CvxLean.Tactic.DCP.DiscrTree
import CvxLean.Tactic.DCP.AtomCurvRule

/-!
# Atom library (environment extension)

This file defines the `GraphAtomData` type, which is what is stored when declaring an atom. Its
fields are curvature and monotonicity attributes and several Lean expressions.

The enviroment extesion is also defined here. We store a discrimination tree built from all the
atoms in the library based on the atom's expression (which is the function that the atom describes).
-/

namespace CvxLean

open Lean Meta

section AtomData

/-- Data structure to store information about registered atoms. -/
structure GraphAtomData where
  id : Name
  curvature : Curvature
  expr : Expr
  argKinds : Array ArgKind
  bconds : Array (Name × Expr)
  vconds : Array (Name × Expr)
  impVars : Array (Name × Expr)
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

/-- Add a new atom to the library (discrimination tree). -/
def addAtom (data : AtomData) : MetaM Unit := do
  let (_, _, expr) ← lambdaMetaTelescope data.expr
  let keys ← DiscrTree.mkPath expr
  setEnv <| atomExtension.addEntry (← getEnv) (keys, data)

/-- Get the atom tree. -/
def getAtomDiscrTree : MetaM (DiscrTree AtomData) := do
  return atomExtension.getState (← getEnv)

end AtomData

end CvxLean
