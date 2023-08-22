import Lean
import Std.Linter.UnreachableTactic
import CvxLean.Tactic.PreDCP.RewriteMapExt

namespace CvxLean

open Lean.Parser

syntax (name := registerRewriteMap) 
  "register_rewrite_map " str " ; " str " => " str " := " tactic : command

open Lean.Elab Lean.Elab.Command

set_option linter.unreachableTactic false in
@[command_elab registerRewriteMap] def elabRegisterEggRewrite : CommandElab
| `(register_rewrite_map $rwName ; $rwTarget => $rwGoal := $tac) => do 
    let rwNameStr := rwName.getString
    -- NOTE(RFM): We ignore this for now.
    let _rwTargetStr := rwTarget.getString
    let _rwGoalStr := rwGoal.getString
    liftTermElabM <| addRewriteMapEntry rwNameStr tac
| _ => throwUnsupportedSyntax

end CvxLean 
