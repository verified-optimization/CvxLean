import Lean

namespace CvxLean

open Lean Lean.Meta

def RewriteMapExtEntry : Type := String × (TSyntax `tactic)
deriving Inhabited

def RewriteMapExtState : Type := HashMap String (TSyntax `tactic)
deriving Inhabited

/-- Environment extension to store the mapping between rewrite names in egg and 
Lean tactics. -/
def RewriteMapExt : Type := 
  SimplePersistentEnvExtension RewriteMapExtEntry RewriteMapExtState
deriving Inhabited

initialize rewriteMapExt : RewriteMapExt ← 
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => 
      mkStateFromImportedEntries (fun s (k, v) => s.insert k v) default as,
    addEntryFn    := fun s (k, v) => s.insert k v,
  }

/-- Add a new rewrite mapping to the environment. -/
def addRewriteMapEntry (rwName : String) (tac : TSyntax `tactic) : MetaM Unit := do
  setEnv <| rewriteMapExt.addEntry (← getEnv) (rwName, tac)

/-- Given rewrite name, return associated tactic in the environment. -/
def getTacticFromRewriteName (rwName : String) : MetaM (Option (TSyntax `tactic)) := do
  return (rewriteMapExt.getState (← getEnv)).find? rwName

/-- Return all the saved rewrite names. -/
def getRegisteredRewriteNames : MetaM (List String) := do
  return (rewriteMapExt.getState (← getEnv)).toList.map (·.1)

end CvxLean
