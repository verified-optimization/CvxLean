import Aesop
import CvxLean.Command.Reduction
import CvxLean.Lib.Missing.Real
import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Tactic.PreDCP.AesopRuleSet

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command
open Aesop
open CvxLean Minimization Real

/-- -/
def isDCP (goal : MVarId) : MetaM Bool := do
  let state ← saveState
  try
    if let [simpedGoal] ← run goal (evalTactic <| ← `(tactic| simp)) |>.run' then
      let _ ← DCP.canonizeGoal simpedGoal
      return true
    else 
      return false
  catch _ =>
    return false
  finally
    restoreState state

/-- -/
def closeIfDCP : RuleTac := fun input =>
  input.goal.withContext do
    let lctx ← getLCtx
    if lctx.decls.size == 1 then
      if let some doneHyp := lctx.decls[0]! then
        if (← isDCP input.goal) then
          let doneId := doneHyp.fvarId
          let state ← saveState
          try
            input.goal.exact (mkFVar doneId)
            let tac := `(tactic| (norm_num_clean_up; exact $(mkIdent <| ← doneId.getUserName)))
            let postState ← saveState
            let scriptBuilder? := mkScriptBuilder? true <| .ofTactic 0 <| tac
            let rapp : RuleApplication := ⟨#[], postState, scriptBuilder?⟩
            return ⟨#[rapp]⟩
          catch _ =>
            return ⟨#[]⟩
          finally restoreState state
    return ⟨#[]⟩

-- Only close goal with custom rule.
attribute [aesop safe (rule_sets [convexify_rule_set]) tactic] closeIfDCP

/-- -/
def applyTargetedRewrite (rwIdx numConstrs : Nat)
  (rwName : String) : RuleTac := fun input =>
  input.goal.withContext do
    let state ← saveState
    try
      let tacStx ← (findTactic rwName EggRewriteDirection.Forward).2
      let (rwWrapper, _) ← rewriteWrapperLemma rwIdx numConstrs

      let gs ← TermElabM.run' <| run input.goal <| do
        let g ← getMainGoal
        let gs ← g.apply (mkConst (`Minimization ++ rwWrapper))

        -- There should be two goals at this point: hrw and cn'.
        if gs.length != 3 then
          throwError ""

        let gToRw := gs[0]!
        let gSol := gs[1]!
        let gExpectedExpr := gs[2]!

        -- Sanity check to make sure we are rewriting in the right place.
        if (← gToRw.getTag) != `hrw then
          throwError ""

        let (_, gToRw) ← gToRw.intros
        dbg_trace "first here {rwName}"
        let tacStx ← `(tactic| $tacStx)
        let gsAfterRw ← evalTacticAt tacStx gToRw

        dbg_trace "second here {rwName} {gsAfterRw.length}"
        
        if gsAfterRw.length != 2 then
          throwError ""

        let realGoals ← getGoals 
        if realGoals.length != 1 then
          dbg_trace "failed {realGoals.length}"
          throwError "r"

        -- If the tactic makes no progress, abort.
        let gToRefl := gsAfterRw[0]!
        let gExpectedExpr' := gsAfterRw[1]!
        dbg_trace "got here {rwName}"
        if gToRw == gToRefl then
          throwError ""

        -- Otherwise, apply rfl to close the goal.
        let gsAfterRfl ← evalTacticAt (← `(tactic| rfl)) gToRefl

        -- If the rewrite is successful, there should be no goals and the expected
        -- expression should be instantiated.
        if gsAfterRfl.length != 0 || !(← gExpectedExpr.isAssigned) || !(← gExpectedExpr'.isAssigned) then
          throwError ""

        dbg_trace "succeeded {rwName}"

        gSol.setTag Name.anonymous
        setGoals [gSol]

      if let [gSol] := gs then
        -- Add rule application.
        let postState ← Meta.saveState
        let fullTac := `(tactic| (apply $(mkIdent rwWrapper); (intros; $tacStx; rfl)))
        let scriptBuilder? := mkScriptBuilder? true <| .ofTactic 1 <| fullTac
        let rapp : RuleApplication := ⟨#[gSol], postState, scriptBuilder?⟩
        return ⟨#[rapp]⟩
      else 
        restoreState state
        return ⟨#[]⟩
    catch _ =>
      restoreState state
      return ⟨#[]⟩

/-- This command adds an Aesop rule for any combination of rewrites, taking all
the rewrites from  -/
syntax (name := add_convexity_aesop_rules) "add_convexity_aesop_rules" : command

@[command_elab «add_convexity_aesop_rules»]
def evalAddConvexityAesopRules : CommandElab := fun stx => match stx with
| `(add_convexity_aesop_rules) => do
    let rwNames := (rewriteMapExt.getState (← getEnv)).toArray.map Prod.fst ++ #["map_objFun_log", "norm_num"]
    for rwName in rwNames do
      for loc in [3:4] do
        for numConstrs in [3:4] do
          -- The number of constraints is irrelevant for the rewrites that
          -- operate on the objective function, so we don't need to consider
          -- all possibilities.
          if loc == 0 && numConstrs > 1 then
            continue
          -- We use `applyTargetedRewrite` to generate new definitions.
          let name := Name.mkSimple <|
            "convexity_rw__" ++ rwName ++ "__" ++ toString loc ++ "_" ++ toString numConstrs
          let name' := mkIdent name
          dbg_trace name'
          let loc' := Lean.Syntax.mkNumLit (toString loc)
          let numConstrs' :=  Lean.Syntax.mkNumLit (toString numConstrs)
          let rwName' := Lean.Syntax.mkStrLit rwName
          elabCommand (← `(def $name' : RuleTac := applyTargetedRewrite $loc' $numConstrs' $rwName'))
          elabCommand (← `(attribute [aesop unsafe (rule_sets [convexify_rule_set]) tactic] $name'))
| _ => throwUnsupportedSyntax

add_convexity_aesop_rules

section Test

def p :=
  optimization (x : ℝ)
    minimize (x)
    subject to
      h0 : 0 ≤ x
      h1 : 0.0001 ≤ x
      h2 : 1 / (sqrt x) ≤ (exp x)


-- def p :=
--   optimization (x y z: ℝ)
--     minimize (x)
--     subject to
--       h2 : (exp x) * (exp y) ≤ exp z

set_option trace.Meta.debug true

set_option trace.aesop.ruleSet true

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
reduction red/q : p := by
  -- unfold p
  -- apply rewrite_constraint_3_last;
  -- { intros;
  --   rewrite [div_le_iff (by positivity)]; rfl }
  -- apply rewrite_constraint_3_last
  -- { intros;
  --   rewrite [mul_comm]; rfl }
  -- apply rewrite_constraint_3_last
  -- { intros;
  --   rewrite [← div_le_iff (by positivity)]; rfl }
  -- apply rewrite_constraint_3_last
  -- { intros;
  --   rewrite [← exp_neg_eq_one_div]; rfl }
  -- norm_num_clean_up -- or simp or dsimp, but why?????
  -- dcp
  -- (apply rewrite_constraint_3_last; (intros; rewrite [div_le_iff (by positivity)]; rfl))
  -- (apply rewrite_constraint_3_last; (intros; rewrite [← Real.log_le_log (by positivity) (by positivity)]; rfl))
  -- (apply rewrite_constraint_3_last; (intros; rewrite [← div_le_one (by positivity)]; rfl))
  -- (norm_num_clean_up; exact done)
  aesop?
    (simp_options := {
      maxDischargeDepth := 0,
      enabled := false })
    (rule_sets [-builtin, -default, convexify_rule_set])
    (options := {
      terminal := true
      strategy := Strategy.breadthFirst,
      maxRuleApplications := 5000,
      maxRuleApplicationDepth := 100 })

end Test

