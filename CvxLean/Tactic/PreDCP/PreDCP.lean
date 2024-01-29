import CvxLean.Lib.Equivalence
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.PreDCP.RewriteMapExt
import CvxLean.Tactic.PreDCP.RewriteMapLibrary
import CvxLean.Tactic.PreDCP.Egg.All
import CvxLean.Tactic.Basic.ConvOpt
import CvxLean.Tactic.Basic.NormNumOpt
import CvxLean.Tactic.Basic.RewriteOpt

/-!
# Atomatic transformation to DCP form

This file defines the tactic `pre_dcp`, which calls `egg` to find a sequence of rewrites that
turns an optimization problem into DCP form.
-/

namespace CvxLean

open Lean Elab Meta Tactic Term IO

/-- Given the rewrite name and direction from egg's output, find the appropriate tactic in the
environment. It also returns a bool to indicate if the proof needs an intermediate equality step.
Otherwise, the tactic will be applied directly. -/
def findTactic (atObjFun : Bool) (rewriteName : String) (direction : EggRewriteDirection) :
    MetaM (TSyntax `tactic × Bool) := do
  match ← getTacticFromRewriteName rewriteName with
  | some (tac, mapObjFun) =>
    if mapObjFun then
      return (tac, true)
    else
      match direction with
      | EggRewriteDirection.Forward => return (tac, false)
      | EggRewriteDirection.Backward =>
          -- Simply flip the goal so that the rewrite is applied to the target.
          if atObjFun then
            return (← `(tactic| (rw [eq_comm]; $tac)), false)
          else
            return (← `(tactic| (rw [Iff.comm]; $tac)), false)
  | _ => throwError "Unknown rewrite name {rewriteName}({direction})."

/-- Given an egg rewrite and a current goal with all the necessary information about the
minimization problem, we find the appropriate rewrite to apply, and output the remaining goals. -/
def evalStep (step : EggRewrite) (vars : List Name) (tagsMap : HashMap String ℕ) :
    EquivalenceBuilder := fun eqvExpr g => g.withContext do
  let tag ← liftMetaM <| do
    if step.location == "objFun" then
      return "objFun"
    else if let [_, tag] := step.location.splitOn ":" then
      return tag
    else
      throwError "`pre_dcp` error: Unexpected tag name {step.location}."
  let tagNum := tagsMap.find! step.location
  let atObjFun := tagNum == 0

  -- Build expexcted expression to generate the right rewrite condition. Again, mapping the
  -- objective function is an exception where the expected term is not used.
  let expectedTermStr := step.expectedTerm
  let mut expectedExpr ← EggString.toExpr vars expectedTermStr
  if !atObjFun then
    expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
  let fvars := Array.mk <| vars.map (fun v => mkFVar (FVarId.mk v))
  -- TODO: Why do we need this?
  let D ← instantiateMVars eqvExpr.domainP
  expectedExpr ← withLocalDeclD `p D fun p => do
    Meta.withDomainLocalDecls D  p fun xs prs => do
      let replacedFVars := Expr.replaceFVars expectedExpr fvars xs
      mkLambdaFVars #[p] (Expr.replaceFVars replacedFVars xs prs)

  let (tacStx, isMap) ← findTactic atObjFun step.rewriteName step.direction

  -- Finally, apply the tactic that should solve all proof obligations. A mix of approaches using
  -- `norm_num` in combination with the tactic provided by the user for this particular rewrite.
  let tacStx : Syntax ← `(tactic| intros;
    try { norm_num_clean_up; $tacStx <;> norm_num_simp_pow } <;>
    try { $tacStx <;> norm_num_simp_pow } <;>
    try { norm_num_simp_pow })

  if isMap then
    -- Maps, e.g., `map_objFun_log` are applied directly to the equivalence goal.
    if let _ :: _ ← evalTacticAt tacStx g then
      throwError "`pre_dcp` error: failed to apply {step.rewriteName}."
  else
    -- Rewrites use the machinery from `Tactic.Basic.RewriteOpt`.
    if atObjFun then
      rewriteObjBuilder true tacStx (some expectedExpr) eqvExpr g
    else
      rewriteConstrBuilder true (Name.mkSimple tag) tacStx (some expectedExpr) eqvExpr g

def preDCPBuilder : EquivalenceBuilder := fun eqvExpr g => g.withContext do
  let lhs ← eqvExpr.toMinimizationExprLHS

  -- Get optimization variables.
  let vars ← withLambdaBody lhs.constraints fun p _ => do
    let pr ← mkProjections lhs.domain p
    return pr.map (Prod.fst)
  let varsStr := vars.map toString

  -- Get optimization parameters. To obtain their domains, we cheat and pretend that any conditions
  -- on the parameters are constraints and use `mkUncheckedTree`.
  let declsNamesAndTypes :=
    (← getLCtx).decls.toList.filterMap (Option.map (fun decl => (decl.userName, decl.type)))
  let paramsNames :=
    (← declsNamesAndTypes.filterM (fun (_, ty) => do return (← inferType ty).isType)).map (·.fst)
  let paramsDecls := (← getLCtx).decls.toArray.filterMap (fun decl? =>
    if let some decl := decl? then
      if decl.userName ∈ paramsNames then some decl else none
    else none)
  let paramsStr := paramsNames.map toString
  let paramsDomainsExpr :=
    (← declsNamesAndTypes.filterM (fun (_, ty) => do return (← inferType ty).isProp)).toArray
  let paramsDomainsOC : OC (Option (Name × Expr)) := OC.mk none (paramsDomainsExpr.map some)
  let potentialParamDomains ← UncheckedDCP.mkUncheckedTree #[] paramsDecls paramsDomainsOC
  let mut paramDomains := #[]
  for c in potentialParamDomains.constr do
    if let some (h, t) := c then
      if let some (_, n, d) := ExtendedEggTree.processDomainExprTree h t paramsStr then
        paramDomains := paramDomains.push (n, d)

  -- Get goal as tree and create tags map.
  let (gStr, domainConstrs) ← ExtendedEggTree.fromMinimization lhs varsStr
  let mut tagsMap := HashMap.empty
  tagsMap := tagsMap.insert "objFun" 0
  let mut idx := 1
  for (h, _) in gStr.constr do
    tagsMap := tagsMap.insert h idx
    idx := idx + 1

  -- Handle domain constraints.
  let varDomainConstrs := domainConstrs.map (fun (_, v, d) => (v, d))
  let constrsToIgnore := domainConstrs.map (fun (h, _, _) => h)

  -- Remove domain constraints before sending it to egg.
  let gStr := { gStr with constr := gStr.constr.filter (fun (h, _) => !constrsToIgnore.contains h) }

  -- Prepare egg request.
  let eggMinimization := EggMinimization.ofOCTree gStr
  let eggRequest : EggRequest :=
    { domains := (varDomainConstrs ++ paramDomains).data,
      target := eggMinimization }

  try
    -- Call egg (time it for evaluation).
    let before ← BaseIO.toIO IO.monoMsNow
    let steps ← runEggRequest eggRequest
    let after ← BaseIO.toIO IO.monoMsNow
    let diff := after - before
    dbg_trace s!"Egg time: {diff} ms."
    dbg_trace s!"Number of steps: {steps.size}."
    let size := (gStr.map fun (_, t) => t.size).fold 0 Nat.add
    dbg_trace s!"Term size: {size}."
    dbg_trace s!"Term JSON: {eggMinimization.toJson}."

    -- Apply steps.
    let mut g := g
    for step in steps do
      let gs ← Tactic.run g <| (evalStep step vars tagsMap).toTactic
      if gs.length != 1 then
        throwError (s!"`pre_dcp` error: failed to rewrite {step.rewriteName} after evaluating "
          ++ s!"step ({gs.length} goals remaining).")
      else
        g := gs[0]!
        dbg_trace s!"Rewrote {step.rewriteName}."

    let gsFinal ← evalTacticAt (← `(tactic| equivalence_rfl)) g
    if gsFinal.length != 0 then
      throwError "`pre_dcp` error: could not close last goal."
  catch e =>
    throwError "`pre_dcp` error: {e.toMessageData}"

/-- The `pre_dcp` tactic encodes a given minimization problem, sends it to egg, and reconstructs
the proof from egg's output. -/
syntax (name := preDCP) "pre_dcp" : tactic

@[tactic preDCP]
def evalPreDCP : Tactic := fun stx => match stx with
  | `(tactic| pre_dcp) => withMainContext do
      normNumOptBuilder.toTactic
      preDCPBuilder.toTactic
      normNumOptBuilder.toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

end CvxLean
