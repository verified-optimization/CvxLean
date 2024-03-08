import Lean
import CvxLean.Tactic.PreDCP.RuleToTacticExt

/-!
# Egg rewrite rule to tactic (command)

This files defines the commands to associate rule names to Lean tactics. There are two commands:
* `register_rule_to_tactic`, for if-and-only-if or real equality rewrites.
* `register_objFun_rule_to_tactic`, for problem-level rewrites (currently these are pre-compositions
  applied to the objective function). They do the same but set the `mapObjFun` flag to `true` in the
  environment extension so that `pre_dcp` knows that it should be applied directly.
-/

namespace CvxLean

open Lean Parser

syntax (name := registerRuleToTactic)
  "register_rule_to_tactic " str ";" str " => " str " := " tactic ";" : command

syntax (name := registerRuleToTacticBidirectional)
  "register_rule_to_tactic " str ";" str " <=> " str " := " tactic ";" : command

macro_rules
  | `(register_rule_to_tactic $rwName; $rwTarget <=> $rwGoal := $tac;) =>
    if let some rwNameStr := Syntax.isStrLit? rwName then
      let rwNameRev := Syntax.mkStrLit (rwNameStr ++ "-rev")
      `(register_rule_to_tactic $rwName; $rwTarget => $rwGoal := $tac;
        register_rule_to_tactic $rwNameRev; $rwGoal => $rwTarget := $tac;)
    else `(throwError "`register_rule_to_tactic` error: expected string.")

syntax (name := registerObjFunRuleToTactic)
  "register_objFun_rule_to_tactic " str ";" str " => " str " := " tactic ";" : command

open Lean.Elab Lean.Elab.Command

@[command_elab registerRuleToTactic] def elabRuleToTactic : CommandElab
| `(register_rule_to_tactic $rwName; $rwTarget => $rwGoal := $tac;) => do
    let rwNameStr := rwName.getString
    -- NOTE: We ignore this for now.
    let _rwTargetStr := rwTarget.getString
    let _rwGoalStr := rwGoal.getString
    liftTermElabM <| addRuleToTacticEntry rwNameStr tac false
| _ => throwUnsupportedSyntax

@[command_elab registerObjFunRuleToTactic] def elabRegisterObjFunRuleToTactic : CommandElab
| `(register_objFun_rule_to_tactic $rwName; $rwTarget => $rwGoal := $tac;) => do
    let rwNameStr := rwName.getString
    -- NOTE: We ignore this for now.
    let _rwTargetStr := rwTarget.getString
    let _rwGoalStr := rwGoal.getString
    liftTermElabM <| addRuleToTacticEntry rwNameStr tac true
| _ => throwUnsupportedSyntax

end CvxLean
