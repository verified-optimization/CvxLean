import CvxLean.Tactic.DCP.DiscrTree

namespace CvxLean

open Lean Lean.Meta

/-- An atom can be affine, concave or convex. -/
inductive Curvature where
  | Affine | Concave | Convex
deriving BEq, Inhabited

/-- Arguments of an atom are increasing (+), decreasing (-), constant (&) or 
neither (?). -/
inductive ArgKind where
  | Increasing | Decreasing | Neither | Constant
deriving BEq, Inhabited

instance : ToMessageData Curvature where 
  toMessageData
  | Curvature.Affine => "affine"
  | Curvature.Concave => "concave"
  | Curvature.Convex => "convex"

instance : ToMessageData ArgKind where 
  toMessageData 
  | ArgKind.Increasing => "increasing"
  | ArgKind.Decreasing => "decreasing"
  | ArgKind.Neither => "neither"
  | ArgKind.Constant => "constant"

/-- Data structure to store information about registered atoms. -/
structure GraphAtomData where
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
deriving BEq, Inhabited

instance : ToMessageData GraphAtomData where
  toMessageData d := 
    m!"curvature: {d.curvature}
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

/-- Caclulate curvature depending on monotonicity. -/
def curvatureInArg : Curvature → ArgKind → Curvature
  | Curvature.Concave, ArgKind.Increasing => Curvature.Concave
  | Curvature.Concave, ArgKind.Decreasing => Curvature.Convex
  | Curvature.Convex, ArgKind.Increasing => Curvature.Convex
  | Curvature.Convex, ArgKind.Decreasing => Curvature.Concave
  | _, _ => Curvature.Affine

end CvxLean
