import Lean

namespace CvxLean

open Lean Lean.Meta

def ConvexifyExtEntry : Type := String × (TSyntax `tactic)
deriving Inhabited

def ConvexifyExtMap : Type := HashMap String (TSyntax `tactic)
deriving Inhabited

/-- Environment extension to store the mapping between rewrite names in egg and 
Lean tactics. -/
def ConvexifyExt : Type := 
  SimplePersistentEnvExtension ConvexifyExtEntry ConvexifyExtMap
deriving Inhabited

initialize convexifyExt : ConvexifyExt ← 
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => 
      mkStateFromImportedEntries (fun s (k, v) => s.insert k v) default as,
    addEntryFn    := fun s (k, v) => s.insert k v,
  }

/-- Add a new atom to the library. -/
def addConvexifyRewrite (rwName : String) (tac : TSyntax `tactic) : MetaM Unit := do
  setEnv $ convexifyExt.addEntry (← getEnv) (rwName, tac)

end CvxLean
