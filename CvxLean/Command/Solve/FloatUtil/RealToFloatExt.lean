import CvxLean.Tactic.DCP.DiscrTree

/-!
# Conversion of Real to Float (environment extension)

This files defines the persistent environment extension used to store the real-to-float translation.
-/

namespace CvxLean

open Lean Meta

/-- Data structure to store the real-to-float translation. -/
structure RealToFloatData where
  real : Expr
  float : Expr
deriving BEq, Inhabited

instance : ToMessageData RealToFloatData where
  toMessageData := fun d =>
    m!"real: {d.real}
    float: {d.float}"

/-- Type of persistent environment extension for real-to-float. We use a discrimination tree. -/
def RealToFloatExtension :=
  PersistentEnvExtension
    (Array Key × RealToFloatData) (Array Key × RealToFloatData) (DiscrTree RealToFloatData)
deriving Inhabited

initialize realToFloatExtension : RealToFloatExtension ← do
  registerPersistentEnvExtension {
    name            := `realToFloatExtension
    mkInitial       := return {}
    addImportedFn   := fun as _ctx =>
      return mkStateFromImportedEntries (fun s d => s.insertCore d.1 d.2) {} as,
    addEntryFn      := fun s d => s.insertCore d.1 d.2,
    exportEntriesFn := fun s => s.toArray
  }

/-- Add a new real-to-float translation to the environment. -/
def addRealToFloatData (data : RealToFloatData) : MetaM Unit := do
  let (_, _, expr) ← lambdaMetaTelescope data.real
  let keys ← DiscrTree.mkPath expr
  setEnv <| realToFloatExtension.addEntry (← getEnv) (keys, data)

/-- Get the discrimination tree of all real-to-float translations. -/
def getRealToFloatDiscrTree : MetaM (DiscrTree RealToFloatData) := do
  return realToFloatExtension.getState (← getEnv)

end CvxLean
