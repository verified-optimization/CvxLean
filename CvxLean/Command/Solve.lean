import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.Solver.Conic
import CvxLean.Command.Reduction

namespace CvxLean

open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta

open Minimization

/-- Equivalent to the `#reduce` command. TODO: Move. -/
def reduceExpr (e : Expr) : MetaM Expr :=
  withTransparency (mode := TransparencyMode.all) <| 
    reduce e (skipProofs := true) (skipTypes := true)

/-- Reduce like `Meta.DiscrTree.whnfDT`. -/
partial def whnfUntilValue (e : Expr) : MetaM Expr := do
  let e ← step e
  match e.etaExpandedStrict? with
  | some e => whnfUntilValue e
  | none   => return e
where
  step (e : Expr) := do
    let e ← whnfCore e
    match (← unfoldDefinition? e) with
    | some e' => if isBadKey e'.getAppFn then return e else step e'
    | none    => return e
  isBadKey (fn : Expr) : Bool :=
    match fn with
    | Expr.lit ..   => false
    | Expr.const .. => false
    | Expr.fvar ..  => false
    | Expr.proj ..  => false
    | Expr.forallE _ _ b _ => b.hasLooseBVars
    | _ => true

/-- Get problem name. Used to add information about the solution to the 
environment. -/
def getProblemName (term : Syntax) : MetaM Lean.Name := do 
  -- TODO: Full name with paraemters.
  let idStx := match term with 
    | Syntax.ident _ _ _ _ => term
    | Syntax.node _ _ args => args.getD 0 Syntax.missing
    | _ => Syntax.missing
  if ¬ idStx.getId.isStr then 
    throwError "Invalid name for minimization problem: {idStx}."

  return idStx.getId

/-- Get solution expression and reduction expression from optimization problem. 
-/
-- NOTE(RFM): Also send backwardMap.
def getReducedProblemAndReduction (prob : Expr) 
: MetaM (Meta.SolutionExpr × Expr × Expr) := do
  let probTy ← inferType prob
  if ¬ probTy.isAppOf ``Minimization then 
    throwError "The command `solve` expects a minimization."
  
  let domain := probTy.getArg! 0 
  let codomain := probTy.getArg! 1
  
  let codomainPreorderInst ← mkFreshExprMVar
    (some $ mkAppN (Lean.mkConst ``Preorder ([levelZero] : List Level)) #[codomain])

  let probSol := mkAppN 
    (mkConst ``Minimization.Solution) 
    #[domain, codomain, codomainPreorderInst, prob]

  let probOpt ← Meta.matchSolutionExprFromExpr probSol
  trace[Meta.debug] "probOpt: {probOpt.objFun}"
  -- NOTE(RFM): We should get the value from this applied to the float sol point.

  let (_, (forwardMap, backwardMap, probReduction)) ← DCP.canonizeGoalFromExpr probSol
  
  let probReducedSol := match (← inferType probReduction) with 
  | Expr.forallE _ r _ _ => r 
  | _ => default

  return (← Meta.matchSolutionExprFromExpr probReducedSol, probReduction, backwardMap)

/-- Add problem declaration inferring type. -/
def addProblemDeclaration (n : Lean.Name) (e : Expr) (compile : Bool) 
: MetaM Unit := do
  let ty ← inferType e 
  let reducibility := Lean.ReducibilityHints.regular 0
  let safety := DefinitionSafety.safe
  let defVal := mkDefinitionValEx n ([] : List Lean.Name) ty e reducibility safety ([n] : List Lean.Name)
  let decl := Declaration.defnDecl defVal
  if compile then
    Lean.addAndCompile decl 
  else 
    Lean.addDecl decl

syntax (name := solve) "solve " term : command

set_option maxHeartbeats 1000000

@[command_elab «solve»]
unsafe def evalSolve : CommandElab := fun stx =>
  match stx with
  | `(solve $probInstance) =>
    liftTermElabM <| do 
      let probTerm ← elabTerm probInstance.raw none
      let probTerm ← whnf probTerm
      let probTerm ← instantiateMVars probTerm

      -- NOTE(RFM): Needed to solve the "OfNat" mvar bug.
      for mvarId in ← getMVars probTerm do 
        try {
          let mvarVal ← synthInstance (← mvarId.getDecl).type
          mvarId.assign mvarVal }
        catch _ => pure ()

      -- Create prob.reduced.
      let (probReducedExpr, probReduction, backwardMap) ← 
        getReducedProblemAndReduction probTerm

      -- Expression of type Minimization.
      let probReducedOpt := probReducedExpr.toMinExpr

      let probName ← getProblemName probInstance.raw
      
      addProblemDeclaration (probName ++ `reduced) probReducedOpt false

      -- Call the solver on prob.reduced and get a point in E.
      let coeffsData ← determineCoeffsFromExpr probReducedExpr
      trace[Meta.debug] "coeffsData: {coeffsData}"
      let solPointResponse ← Meta.conicSolverFromValues probReducedExpr coeffsData
      trace[Meta.debug] "solPointResponse: {solPointResponse}"
      
      match solPointResponse with 
      | Sol.Response.failure code => 
        trace[Meta.debug] "MOSEK failed with code {code}"
        pure ()

      -- Mosek finished successfully.
      | Sol.Response.success solPoint =>
        trace[Meta.debug] "solPoint.summary: {solPoint.summary}"

        -- Add status to the environment. 
        addProblemDeclaration 
          (probName ++ `status) (mkStrLit solPoint.summary.problemStatus) true
        
        -- TODO: For now, we are only handling this case. 
        if solPoint.summary.problemStatus != "PRIMAL_AND_DUAL_FEASIBLE" then 
          pure ()

        -- Solution makes sense, handle the numerical solution.
        let solPointExpr ← Meta.exprFromSol probReducedExpr solPoint

        let probSolPointFloat ← whnf <| ← realToFloat <| mkAppN backwardMap #[solPointExpr]

        -- Add the solution point to the environment.
        addProblemDeclaration (probName ++ `solution) probSolPointFloat true

        -- Also add value of optimal point.
        trace[Meta.debug] "probReducedExpr.objFun {probReducedExpr.objFun}"
        let probSolValue := mkApp probReducedExpr.objFun solPointExpr
        let probSolValueFloat ← realToFloat probSolValue
        trace[Meta.debug] "probSolValueFloat {probSolValueFloat}"
        check probSolValueFloat
        let mut probSolValueFloat := Expr.headBeta probSolValueFloat
        trace[Meta.debug] "probSolValueFloat reduced: {probSolValueFloat}"
        if probSolValueFloat.getAppFn.isConstOf `CvxLean.maximizeNeg then 
          probSolValueFloat := probSolValueFloat.getAppArgs[2]!
        addProblemDeclaration (probName ++ `value) probSolValueFloat true

        pure ()
  | _ => throwUnsupportedSyntax

end CvxLean
