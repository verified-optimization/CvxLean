import CvxLean.Tactic.Basic.ShowVars

namespace CvxLean

namespace Tactic.Conv

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta

syntax (name := showVars) "show_vars" ident : conv

/-- Like the basic `show_vars` but as a conv tactic. -/
@[tactic showVars]
partial def evalShowVars : Tactic
| `(conv| show_vars $p) => do
  replaceMainGoal [← Meta.showVars (← getMainGoal) (← withMainContext do getFVarId p)]
| _ => throwUnsupportedSyntax

end Tactic.Conv

end CvxLean
