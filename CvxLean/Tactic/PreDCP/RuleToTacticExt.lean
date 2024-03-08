import Lean

/-!
# Egg rewrite rule to tactic (environment extension)

This files defines the persistent environment extension used to store translation of `egg` rewrite
rule names to Lean tactics.
-/

namespace CvxLean

open Lean Meta

/-- An entry is the name of the rewrite, the corresponding tactic, and whether
it is an objective function map or not. -/
def RuleToTacticExtEntry : Type := String × ((TSyntax `tactic) × Bool)
deriving Inhabited

def RuleToTacticExtState : Type := HashMap String ((TSyntax `tactic) × Bool)
deriving Inhabited

/-- Environment extension to store the mapping between rewrite names in egg and
Lean tactics. -/
def RuleToTacticExt : Type :=
  SimplePersistentEnvExtension RuleToTacticExtEntry RuleToTacticExtState
deriving Inhabited

initialize ruleToTacticExt : RuleToTacticExt ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as =>
      mkStateFromImportedEntries (fun s (k, v) => s.insert k v) default as,
    addEntryFn    := fun s (k, v) => s.insert k v,
  }

/-- Add a new rewrite mapping to the environment. -/
def addRuleToTacticEntry (rwName : String) (tac : TSyntax `tactic) (mapObjFun : Bool) :
    MetaM Unit := do
  setEnv <| ruleToTacticExt.addEntry (← getEnv) (rwName, (tac, mapObjFun))

/-- Given rewrite name, return associated tactic in the environment. -/
def getTacticFromRewriteName (rwName : String) : MetaM (Option (TSyntax `tactic × Bool)) := do
  return (ruleToTacticExt.getState (← getEnv)).find? rwName

/-- Return all the saved rewrite names. -/
def getRegisteredRewriteNames : MetaM (List String) := do
  return (ruleToTacticExt.getState (← getEnv)).toList.map (·.1)

end CvxLean
