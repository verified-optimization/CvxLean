import Aesop
import CvxLean.Command.Reduction
import CvxLean.Lib.Missing.Real
import CvxLean.Tactic.DCP.Dcp
import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.PreDCP.Convexify

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

-- Ignore assumptions.
attribute [-aesop] Aesop.BuiltinRules.applyHyps
attribute [-aesop] Aesop.BuiltinRules.assumption

-- Only close goal with custom rule.
attribute [aesop safe tactic] closeIfDCP

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
      dbg_trace "got here"
      -- There should be two goals at this point: hrw and cn'.
      if gs.length != 2 then
        return ⟨#[]⟩
      
      let gToRw := gs[0]!
      let gExpectedExpr := gs[1]!

      -- Sanity check to make sure we are rewriting in the right place.
      if (← gToRw.getTag) != `hrw then
        dbg_trace "hrw tag not found"
        return ⟨#[]⟩
      
      let tacStx ← `(tactic| (intros; $tacStx)) 
      let gsAfterRw ← Meta.runTactic gToRw (evalTacticAt tacStx)

      -- If the rewrite is successful, there should be no goals and the expected
      -- expression should be instantiated.
      if gsAfterRw.length != 0 || !(← gExpectedExpr.isAssigned) then
        return ⟨#[]⟩

      -- Add rule application.
      let postState ← saveState
      let fullTacStx ← `(tactic| (apply $(mkIdent rwWrapper); $tacStx))
      let scriptBuilder? := mkScriptBuilder? true <| .ofTactic 1 <| 
              withTransparencySyntax TransparencyMode.default <| fullTacStx
      let rapp : RuleApplication := ⟨#[], postState, scriptBuilder?⟩ 
      return ⟨#[rapp]⟩
    catch _ => 
      return ⟨#[]⟩
    finally 
      restoreState state


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
          -- let type : Expr := mkConst `RuleTac
          -- let value : Expr := mkAppN 
          --   (mkConst `applyTargetedRewrite) 
          --   #[mkNatLit loc, mkNatLit numConstrs, mkStrLit rwName]
          -- let reducibility := Lean.ReducibilityHints.regular 0
          -- let safety := DefinitionSafety.safe
          -- Lean.addDecl <| 
          --   Declaration.defnDecl 
          --   (mkDefinitionValEx name [] type value reducibility safety [])
          let name' := mkIdent name
          dbg_trace name'
          let loc' := Lean.Syntax.mkNumLit (toString loc)
          let numConstrs' :=  Lean.Syntax.mkNumLit (toString numConstrs)
          let rwName' := Lean.Syntax.mkStrLit rwName
          elabCommand (← `(def $name' : RuleTac := applyTargetedRewrite $loc' $numConstrs' $rwName'))
          elabCommand (← `(attribute [aesop unsafe tactic] $name'))    
| _ => throwUnsupportedSyntax

add_convexity_aesop_rules

#print convexity_rw__map_objFun_log__0_1

section Test

def p := 
  optimization (x : ℝ)
    minimize (x)
    subject to   
      h1 : 0 < x
      h2 : 1 / (sqrt x) ≤ (exp x)

set_option trace.Meta.debug true

reduction red/q : p := by
  aesop? (options := { maxRuleApplicationDepth := 100 })

end Test

end Test 

