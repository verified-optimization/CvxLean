import Lean
import Std.Linter.UnreachableTactic
import CvxLean.Tactic.PreDCP.RewriteMapExt

namespace CvxLean

open Lean Parser

syntax (name := registerRewriteMap)
  "register_rewrite_map " str " ; " str " => " str " := " tactic ";" : command

syntax (name := registerRewriteMapBidirectional)
  "register_rewrite_map " str " ; " str " <=> " str " := " tactic ";" : command

macro_rules
  | `(register_rewrite_map $rwName ; $rwTarget <=> $rwGoal := $tac;) =>
    if let some rwNameStr := Syntax.isStrLit? rwName then
      let rwNameRev := Syntax.mkStrLit (rwNameStr ++ "-rev")
      `(register_rewrite_map $rwName ; $rwTarget => $rwGoal := $tac;
        register_rewrite_map $rwNameRev ; $rwGoal => $rwTarget := $tac;)
    else `(throwError "register_rewrite_map error: expected string")

syntax (name := registerObjFunRewriteMap)
  "register_objFun_rewrite_map " str " ; " str " => " str " := " tactic ";" : command

open Lean.Elab Lean.Elab.Command

set_option linter.unreachableTactic false in
@[command_elab registerRewriteMap] def elabRegisterEggRewrite : CommandElab
| `(register_rewrite_map $rwName ; $rwTarget => $rwGoal := $tac;) => do
    let rwNameStr := rwName.getString
    -- NOTE: We ignore this for now.
    let _rwTargetStr := rwTarget.getString
    let _rwGoalStr := rwGoal.getString
    liftTermElabM <| addRewriteMapEntry rwNameStr tac false
| _ => throwUnsupportedSyntax

set_option linter.unreachableTactic false in
@[command_elab registerObjFunRewriteMap] def elabRegisterObjFunEggRewrite : CommandElab
| `(register_objFun_rewrite_map $rwName ; $rwTarget => $rwGoal := $tac;) => do
    let rwNameStr := rwName.getString
    -- NOTE: We ignore this for now.
    let _rwTargetStr := rwTarget.getString
    let _rwGoalStr := rwGoal.getString
    liftTermElabM <| addRewriteMapEntry rwNameStr tac true
| _ => throwUnsupportedSyntax

end CvxLean
