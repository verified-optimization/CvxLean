import CvxLean.Lib.Equivalence
import CvxLean.Meta.Equivalence
import CvxLean.Meta.TacticBuilder
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Util.Debug
import CvxLean.Tactic.PreDCP.RuleToTacticExt
import CvxLean.Tactic.PreDCP.RuleToTacticLibrary
import CvxLean.Tactic.PreDCP.Egg.All
import CvxLean.Tactic.Basic.ConvOpt
import CvxLean.Tactic.Basic.NormNumOpt
import CvxLean.Tactic.Basic.RewriteOpt

/-!
# Automatic transformation to DCP form

This file defines the tactic `pre_dcp`, which calls `egg` to find a sequence of rewrites that
turns an optimization problem into DCP form.

### TODO

* Currently, the tactic immediately fails if it cannot prove some side condition, we could instead
  leave them as goals for the user to prove manually. Assuming that the interval arithmetic used on
  the `egg` side is correct, they should all be provable.
-/

namespace CvxLean

open Lean Elab Meta Tactic Term IO

/-- Given the rewrite name and direction from egg's output, find the appropriate tactic in the
environment. It also returns a bool to indicate if the proof needs an intermediate equality step.
Otherwise, the tactic will be applied directly. -/
def findTactic (rewriteName : String) (direction : EggRewriteDirection) :
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
          return (← `(tactic| (symm; $tac)), false)
  | _ => throwPreDCPError "unknown rewrite name {rewriteName}({direction})."

/-- Given an egg rewrite and a current goal with all the necessary information about the
minimization problem, we find the appropriate rewrite to apply, and output the remaining goals. -/
def evalStep (step : EggRewrite) (vars params : List Name) (paramsDecls : List LocalDecl)
    (tagsMap : HashMap String ℕ) : EquivalenceBuilder Unit := fun eqvExpr g => g.withContext do
  let tag ← liftMetaM <| do
    if step.location == "objFun" then
      return "objFun"
    else if let [_, tag] := step.location.splitOn ":" then
      return tag
    else
      throwPreDCPError "unexpected tag name {step.location}."
  let tagNum := tagsMap.find! step.location
  let atObjFun := tagNum == 0

  let (tacStx, isMap) ← findTactic step.rewriteName step.direction

  -- This tactic should solve the final goal. It uses the tactic provided by the user for this
  -- particular rule in combination with `norm_num`.
  let tacStx : Syntax ← `(tactic|
    try { $tacStx <;> norm_num_simp_pow } <;>
    try { norm_num_simp_pow })

  if isMap then
    -- Maps, e.g., `map_objFun_log` are applied directly to the equivalence goal.
    if let gs@(_ :: _) ← evalTacticAt tacStx g then
      trace[CvxLean.debug] "`pre_dcp` failed to close goals: {gs}."
      throwPreDCPError "failed to apply {step.rewriteName}."
  else
    -- Optimization and param free variables, and domain. Needed to build expressions and replace
    -- variables appropriately.
    let fvars := Array.mk <| vars.map (fun v => mkFVar (FVarId.mk v))
    let paramsFvars := Array.mk <| params.map (fun v => mkFVar (FVarId.mk v))
    let paramsDeclsIds := Array.mk <| paramsDecls.map (fun decl => mkFVar decl.fvarId)
    let D ← instantiateMVars eqvExpr.domainLHS

    -- Convert string subexpressions given by `egg` into expressions.
    let mut lhsSubExpr ← EggString.toExpr vars params step.subexprFrom
    let mut rhsSubExpr ← EggString.toExpr vars params step.subexprTo
    lhsSubExpr ← withLocalDeclD `p D fun p => do
      Meta.withDomainLocalDecls D p fun xs prs => do
        let lhsSubExpr := Expr.replaceFVars lhsSubExpr paramsFvars paramsDeclsIds
        let lhsSubExpr := Expr.replaceFVars lhsSubExpr fvars xs
        let lhsSubExpr := Expr.replaceFVars lhsSubExpr xs prs
        mkLambdaFVars #[p] lhsSubExpr
    rhsSubExpr ← withLocalDeclD `p D fun p => do
      Meta.withDomainLocalDecls D p fun xs prs => do
        let rhsSubExpr := Expr.replaceFVars rhsSubExpr paramsFvars paramsDeclsIds
        let rhsSubExpr := Expr.replaceFVars rhsSubExpr fvars xs
        let rhsSubExpr := Expr.replaceFVars rhsSubExpr xs prs
        mkLambdaFVars #[p] rhsSubExpr

    -- Build expexcted expression to generate the right rewrite condition. Note that this has a hole
    -- where the subexpression will be placed. For example, if
    let mut expectedExpr ← EggString.toExpr vars params step.expectedTerm
    if !atObjFun then
      expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
    expectedExpr ←
      withLocalDeclD `p D fun p => do
        Meta.withDomainLocalDecls D p fun xs prs => do
          let expectedExpr := Expr.replaceFVars expectedExpr paramsFvars paramsDeclsIds
          let expectedExpr := Expr.replaceFVars expectedExpr fvars xs
          let expectedExpr := Expr.replaceFVars expectedExpr xs prs
          withLocalDeclD `subexpr (← inferType (rhsSubExpr.mkAppNBeta #[p])) fun subexpr =>
            let expectedExpr := expectedExpr.replaceFVars #[mkFVar (FVarId.mk `subexpr)] #[subexpr]
            mkLambdaFVars #[p, subexpr] expectedExpr

    -- The target expression is the expected expression above replacing `subexpr` with the
    -- right-hand side subexpression.
    let targetExpr ← withLocalDeclD `p D fun p => do
      let targetExpr := expectedExpr.mkAppNBeta #[p, rhsSubExpr.mkAppNBeta #[p]]
      mkLambdaFVars #[p] targetExpr

    -- This tactic first uses congruence to reduce the goal to the equality of the subexpressions
    -- and then applies `tacStx`.
    let tac : MVarId → FVarId → TacticM Unit := fun g p => do
      -- Introduce other constraints.
      let (_, g) ← g.intros
      let mut g := g
      -- Apply optimization variables to expresssions.
      let lhsSubExprAtProb := lhsSubExpr.mkAppNBeta #[mkFVar p]
      let rhsSubExprAtProb := rhsSubExpr.mkAppNBeta #[mkFVar p]
      let expectedExprAtProb := expectedExpr.mkAppNBeta #[mkFVar p]
      -- Distinguish between rewriting props and reals. No need to apply congruence if we are
      -- rewriting the whole constraint.
      if !(← inferType lhsSubExprAtProb).isProp then
        -- Reduce to equality goal for real rewrites .
        if !atObjFun then
          let gs ← g.apply (mkConst ``Iff.of_eq)
          if gs.length != 1 then
            throwPreDCPError "failed to apply `iff_of_eq`."
          g := gs[0]!
        -- Apply congruence.
        let subExprAtProbType ← inferType rhsSubExprAtProb
        let congrLemma ← mkAppOptM ``congrArg
          #[subExprAtProbType, none, lhsSubExprAtProb, rhsSubExprAtProb, expectedExprAtProb]
        let gs ← g.apply congrLemma
        if gs.length != 1 then
          throwPreDCPError "failed to apply `congrArg`."
        g := gs[0]!
      -- Apply the tactic.
      let gs ← evalTacticAt tacStx g
      if gs.length != 0 then
        trace[CvxLean.debug] "`pre_dcp` failed to close goals: {gs}."
        throwPreDCPError "failed to apply {step.rewriteName}."
      pure ()

    -- Rewrites use the machinery from `Tactic.Basic.RewriteOpt`.
    if atObjFun then
      rewriteObjBuilderFromTactic true tac targetExpr eqvExpr g
    else
      let _ ← rewriteConstrBuilderFromTactic true (Name.mkSimple tag) tac targetExpr eqvExpr g

def preDCPBuilder : EquivalenceBuilder Unit := fun eqvExpr g => g.withContext do
  let lhs ← eqvExpr.toMinimizationExprLHS

  -- Get optimization variables.
  let varsNames ← withLambdaBody lhs.constraints fun p _ => do
    let pr ← mkProjections lhs.domain p
    return pr.map (Prod.fst)
  let varsStr := varsNames.map toString

  -- Get optimization parameters. To obtain their domains, we cheat and pretend that any conditions
  -- on the parameters are constraints and use `mkUncheckedTree`.
  let declsNamesAndTypes :=
    (← getLCtx).decls.toList.filterMap (Option.map (fun decl => (decl.userName, decl.type)))
  let paramsNames :=
    (← declsNamesAndTypes.filterM (fun (_, ty) => do return (← inferType ty).isType)).map (·.fst)
  let paramsDecls := (← getLCtx).decls.toList.filterMap (fun decl? =>
    if let some decl := decl? then
      if decl.userName ∈ paramsNames then some decl else none
    else none)
  let paramsStr := paramsNames.map toString
  let paramsDomainsExpr :=
    (← declsNamesAndTypes.filterM (fun (_, ty) => do return (← inferType ty).isProp)).toArray
  let paramsDomainsOC : OC (Option (Name × Expr)) := OC.mk none (paramsDomainsExpr.map some)
  let potentialParamDomains ← UncheckedDCP.mkUncheckedTree #[] paramsDecls.toArray paramsDomainsOC
  let mut paramDomains := #[]
  for c in potentialParamDomains.constr do
    if let some (h, t) := c then
      if let some ⟨_, n, d⟩ := EggOCTreeExtended.processDomainExprTree h t paramsStr then
        paramDomains := paramDomains.push (n, d)

  -- Get goal as tree and create tags map.
  let (gStr, domainConstrs) ← EggOCTreeExtended.fromMinimization lhs varsStr
  let probSize := (gStr.map fun (_, t) => t.size).fold 0 Nat.add
  let mut tagsMap := HashMap.empty
  tagsMap := tagsMap.insert "objFun" 0
  let mut idx := 1
  for (h, _) in gStr.constr do
    tagsMap := tagsMap.insert h idx
    idx := idx + 1

  -- Handle domain constraints.
  let varDomainConstrs := domainConstrs.map (fun ⟨_, v, d⟩ => (v, d))
  let constrsToIgnore := domainConstrs.map (fun ⟨h, _, _⟩ => h)

  -- Remove domain constraints before sending it to egg.
  let gStr := { gStr with constr := gStr.constr.filter (fun (h, _) => !constrsToIgnore.contains h) }

  -- Prepare `egg` request.
  let eggMinimization := EggMinimization.ofEggOCTree gStr
  let eggRequest : EggRequest :=
    { domains := (varDomainConstrs ++ paramDomains).data,
      target := eggMinimization }

  try
    -- Call `egg` (time it for evaluation).
    let bef ← BaseIO.toIO IO.monoMsNow
    let steps ← runEggRequest eggRequest
    let aft ← BaseIO.toIO IO.monoMsNow
    let diff := aft - bef
    dbg_trace s!"Egg time: {diff} ms."
    dbg_trace s!"Number of steps: {steps.size}."
    dbg_trace s!"Term size: {probSize}."
    dbg_trace s!"Term JSON: {eggMinimization.toJson}."

    -- Apply steps.
    let mut g := g
    for step in steps do
      let gs ← Tactic.run g <| (evalStep step varsNames paramsNames paramsDecls tagsMap).toTactic
      if gs.length != 1 then
        trace[CvxLean.debug] "Remaining goals: {gs}."
        throwPreDCPError "failed to rewrite {step.rewriteName} ({gs.length} goals remaining)."
      else
        trace[CvxLean.debug] "Rewrote {step.rewriteName}."
        g := gs[0]!

    let gsFinal ← evalTacticAt (← `(tactic| equivalence_rfl)) g
    if gsFinal.length != 0 then
      trace[CvxLean.debug] "Remaining goals: {gsFinal}."
      throwPreDCPError "could not close last goal."
  catch e =>
    throwPreDCPError "{e.toMessageData}"

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
