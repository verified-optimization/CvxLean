import Lean

namespace CvxLean

open Lean Lean.Meta

/-- An entry is the name of the rewrite, the corresponding tactic, and whether
it is an objective function map or not. -/
def RewriteMapExtEntry : Type := String × ((TSyntax `tactic) × Bool)
deriving Inhabited

def RewriteMapExtState : Type := HashMap String ((TSyntax `tactic) × Bool)
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
def addRewriteMapEntry (rwName : String) (tac : TSyntax `tactic) (mapObjFun : Bool) : MetaM Unit := do
  setEnv <| rewriteMapExt.addEntry (← getEnv) (rwName, (tac, mapObjFun))

/-- Given rewrite name, return associated tactic in the environment. -/
def getTacticFromRewriteName (rwName : String) : MetaM (Option (TSyntax `tactic × Bool)) := do
  return (rewriteMapExt.getState (← getEnv)).find? rwName

/-- Return all the saved rewrite names. -/
def getRegisteredRewriteNames : MetaM (List String) := do
  return (rewriteMapExt.getState (← getEnv)).toList.map (·.1)

end CvxLean
