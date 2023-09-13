import Aesop
import CvxLean.Command.Reduction
import CvxLean.Lib.Missing.Real
import CvxLean.Tactic.DCP.Dcp
import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Tactic.PreDCP.AesopRuleSet

open Lean Lean.Elab Lean.Meta Lean.Elab.Tactic Lean.Elab.Term Lean.Elab.Command
open Aesop
open CvxLean Minimization Real

/-- -/
def isDCP (goal : MVarId) : MetaM Bool := do
  let state ← saveState
  try 
    let _ ← DCP.canonizeGoal goal
    return true
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
            let tac ← `(tactic| exact $(mkIdent <| ← doneId.getUserName))
            let postState ← saveState 
            let scriptBuilder? := mkScriptBuilder? true <| .ofTactic 1 <| 
              withTransparencySyntax TransparencyMode.default <| tac
            let rapp : RuleApplication := ⟨#[], postState, scriptBuilder?⟩ 
            return ⟨#[rapp]⟩ 
          catch _ => 
            return ⟨#[]⟩
          finally restoreState state
    return ⟨#[]⟩

-- Only close goal with custom rule.
attribute [aesop safe (rule_sets [convexify_rule_set]) tactic] closeIfDCP

lemma x : (1 + 1) = 1 ↔ 2 = 1:= by rfl

/-- -/
def applyTargetedRewrite (rwIdx numConstrs : Nat) 
  (rwName : String) : RuleTac := fun input =>
  input.goal.withContext do 
    let state ← saveState
    try 
      let (_, tac) := findTactic rwName EggRewriteDirection.Forward
      let tacStx ← tac 
      let (rwWrapper, _) ← rewriteWrapperLemma rwIdx numConstrs
      let gs ← input.goal.apply (mkConst (`Minimization ++ rwWrapper))
      
      -- There should be two goals at this point: hrw and cn'.
      if gs.length != 3 then
        restoreState state
        return ⟨#[]⟩
      
      let gToRw := gs[0]!
      let gSol := gs[1]!
      let gExpectedExpr := gs[2]!

      -- Sanity check to make sure we are rewriting in the right place.
      if (← gToRw.getTag) != `hrw then
        dbg_trace "hrw tag not found {← gToRw.getTag}"
        restoreState state
        return ⟨#[]⟩
      
      dbg_trace "got here {rwName}"
      let tacStx ← `(tactic| (intros; $tacStx <;> rfl)) 
      let gsAfterRw ← Meta.runTactic gToRw (evalTacticAt tacStx)
      dbg_trace "applied {rwName}"

      -- If the rewrite is successful, there should be no goals and the expected
      -- expression should be instantiated.
      if gsAfterRw.length != 0 || !(← gExpectedExpr.isAssigned) then
        
        restoreState state
        return ⟨#[]⟩
      
      dbg_trace "succeeded {rwName}"
      
      gSol.setTag Name.anonymous
      
      -- Add rule application.
      let postState ← saveState
      let fullTacStx ← `(tactic| (apply $(mkIdent rwWrapper); $tacStx))
      let scriptBuilder? := mkScriptBuilder? true <| .ofTactic 1 <| 
              withTransparencySyntax TransparencyMode.default <| fullTacStx

      let rapp : RuleApplication := ⟨#[gSol], postState, scriptBuilder?⟩ 
      return ⟨#[rapp]⟩
    catch _ => 
      restoreState state
      return ⟨#[]⟩

/-- This command adds an Aesop rule for any combination of rewrites, taking all
the rewrites from  -/
syntax (name := add_convexity_aesop_rules) "add_convexity_aesop_rules" : command

@[command_elab «add_convexity_aesop_rules»]
def evalAddConvexityAesopRules : CommandElab := fun stx => match stx with
| `(add_convexity_aesop_rules) => do
    let rwNames := (rewriteMapExt.getState (← getEnv)).toArray.map Prod.fst ++ #["map_objFun_log"]
    for rwName in rwNames do 
      for loc in [0:4] do 
        for numConstrs in [1:4] do 
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

-- def p := 
--   optimization (x : ℝ)
--     minimize (x)
--     subject to   
--       h1 : 0 < x
--       h2 : 1 / (sqrt x) ≤ (exp x)

def p := 
  optimization (x : ℝ)
    minimize (x)
    subject to
      h2 : (exp x) * (exp x) ≤ exp x 

set_option trace.Meta.debug true

#check Aesop.SimpConfig

#check Real.exp_add

set_option trace.aesop.ruleSet true

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
reduction red/q : p := by
  aesop? 
    (simp_options := { 
      maxDischargeDepth := 0,
      enabled := false })
    (rule_sets [-builtin, -default, convexify_rule_set])
    (options := { 
      strategy := Strategy.breadthFirst,
      maxRuleApplications := 10000,
      maxRuleApplicationDepth := 100 })

end Test 

