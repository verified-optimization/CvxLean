import CvxLean.Tactic.DCP.DiscrTree

namespace CvxLean

open Lean Lean.Meta

/-- Data structure to store information about registered translation. -/
structure RealToFloatData where
  real : Expr
  float : Expr
deriving BEq, Inhabited

instance : ToMessageData RealToFloatData := {
  toMessageData := fun d =>
    m!"real: {d.real}
    float: {d.float}"
}

def RealToFloatExtension := 
  PersistentEnvExtension 
    (Array Key × RealToFloatData) (Array Key × RealToFloatData) (DiscrTree RealToFloatData)
deriving Inhabited

initialize realToFloatExtension : RealToFloatExtension ← do
  let realToFloatExtension ← registerPersistentEnvExtension {
    name            := `realToFloatExtension
    mkInitial       := return {}
    addImportedFn   := fun as ctx =>
      return mkStateFromImportedEntries 
        (fun (s : DiscrTree RealToFloatData) (d : Array Key × RealToFloatData) => s.insertCore d.1 d.2) {} as,
    addEntryFn      := fun s d => s.insertCore d.1 d.2,
    exportEntriesFn := fun s => s.toArray
  }
  return realToFloatExtension

/-- Add a new translatio. -/
def addRealToFloatData (data : RealToFloatData) : MetaM Unit := do
  let (_, _, expr) ← lambdaMetaTelescope data.real
  let keys ← DiscrTree.mkPath expr
  setEnv $ realToFloatExtension.addEntry (← getEnv) (keys, data)

/-- -/
def getRealToFloatDiscrTree : MetaM (DiscrTree RealToFloatData) := do
  return realToFloatExtension.getState (← getEnv)

end CvxLean
