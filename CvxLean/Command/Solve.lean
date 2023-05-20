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
def getReducedProblemAndReduction (prob : Expr) 
: MetaM (Meta.SolutionExpr × Expr) := do
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

  let (_, probReduction) ← DCP.canonizeGoalFromExpr probSol
  
  let probReducedSol := match (← inferType probReduction) with 
  | Expr.forallE _ r _ _ => r 
  | _ => default

  return (← Meta.matchSolutionExprFromExpr probReducedSol, probReduction)

/-- Add problem declaration inferring type. -/
def addProblemDeclaration (n : Lean.Name) (e : Expr) (compile : Bool) 
: MetaM Unit := do
  let ty ← inferType e 
  let reducibility := Lean.ReducibilityHints.regular 0
  let safety := DefinitionSafety.safe
  let defVal := mkDefinitionValEx n ([] : List Lean.Name) ty e reducibility safety ([] : List Lean.Name)
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

      -- Create prob.reduced.
      let (probReducedExpr, probReduction) ← 
        getReducedProblemAndReduction probTerm

      -- Expression of type Minimization.
      let probReducedOpt := probReducedExpr.toMinExpr

      -- Domain, codomain and optimization problem (useful to build terms).
      let probReducedSignature := 
        #[probReducedExpr.domain, probReducedExpr.codomain, probReducedOpt]

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

        -- Define prob.reduced.fakeSolution : Solution probReduced.

        -- Create sorry'd feasibility proof.
        let fakeFeasibility ← mkSyntheticSorry $ mkAppN (mkConst ``constraints) 
          (probReducedSignature ++ #[solPointExpr])

        -- Create sorry'd optimality proof.
        let feasPointTy := mkAppN (mkConst ``FeasPoint) probReducedSignature
        let objFunFeasPointVal := mkAppN (mkConst ``objFun)
          (probReducedSignature ++ #[solPointExpr])
        let fakeOptimality ← mkSyntheticSorry $ ← withLocalDeclD `y feasPointTy 
          fun y => do
            let hasLe := mkAppN (mkConst ``Preorder.toLE ([levelZero] : List Level)) 
              #[probReducedExpr.codomain, probReducedExpr.codomainPreorder]
            let le := mkAppN (mkConst ``LE.le ([levelZero] : List Level)) 
              #[probReducedExpr.codomain, hasLe]
            let pointVal := mkAppN (mkConst ``FeasPoint.point)
              (probReducedSignature ++ #[y])
            let objFunPointVal := mkAppN (mkConst ``objFun)
              (probReducedSignature ++ #[pointVal])
            mkForallFVars #[y] (mkAppN le #[objFunFeasPointVal, objFunPointVal])
        
        -- Put everything together in a `Solution`.
        let probReducedFakeSol := mkAppN (mkConst ``Solution.mk)
          #[probReducedExpr.domain,
            probReducedExpr.codomain,
            probReducedExpr.codomainPreorder,
            probReducedOpt,
            solPointExpr, 
            fakeFeasibility, 
            fakeOptimality]
        check probReducedFakeSol

        -- Define `prob.fakeSolution` of type `Solution prob` by applying the
        -- reduction, i.e. `probReduction probReduced.fakeSolution`.
        let probFakeSol := mkApp probReduction probReducedFakeSol
        check probFakeSol

        -- Apply `realToFloat` to `prob.fakeSolution.point` and (hopefully) 
        -- obtain a point `y` in `float(D)`.
        let probFakeSolPoint := mkAppN (mkConst ``Solution.point)
          #[probReducedExpr.domain,
            probReducedExpr.codomain,
            probReducedExpr.codomainPreorder,
            probReducedOpt,
            probFakeSol]
        
        trace[Meta.debug] "probFakeSolPoint: {probFakeSolPoint}."
        -- NOTE: Cannot use whnf here because it introduces _Privates...
        let probFakeSolPoint ← whnfUntilValue probFakeSolPoint
        --reduce probFakeSolPoint false false false 
        --whnfUntilValue
        trace[Meta.debug] "probFakeSolPoint reduced: {probFakeSolPoint}."
        let probSolPointFloat ← realToFloat probFakeSolPoint
        let probSolPointFloat ← reduceExpr probSolPointFloat
        trace[Meta.debug] "probSolPointFloat: {probSolPointFloat}."
        check probSolPointFloat
        -- NOTE: This last reduction is only needed if we want the resulting
        -- term to be nice. But can lead to timeouts.
        -- let probSolPointFloat ← reduceExpr probSolPointFloat
        -- trace[Meta.debug] "probSolPointFloat reduced: {probSolPointFloat}."

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
