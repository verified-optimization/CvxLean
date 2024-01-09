import CvxLean.Tactic.DCP.AtomLibrary.All
import CvxLean.Command.Solve.Conic

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

/-- -/
def getReducedProblemAndBwdMap (prob : Expr) : MetaM (Meta.MinimizationExpr × Expr) := do
  let ogProb ← Meta.MinimizationExpr.fromExpr prob

  let (redProb, eqvProof) ← DCP.canonize ogProb

  let backwardMap ← mkAppM ``Minimization.Equivalence.psi #[eqvProof]

  return (redProb, backwardMap)

/-- Add problem declaration inferring type. -/
def addProblemDeclaration (n : Lean.Name) (e : Expr) (compile : Bool) : MetaM Unit := do
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

      -- NOTE: Needed to solve the "OfNat" mvar bug.
      for mvarId in ← getMVars probTerm do
        try {
          let mvarVal ← synthInstance (← mvarId.getDecl).type
          mvarId.assign mvarVal }
        catch _ => pure ()

      -- Create prob.reduced.
      let (redProb, backwardMap) ← getReducedProblemAndBwdMap probTerm
      let redProbExpr := redProb.toExpr

      let probName ← getProblemName probInstance.raw

      addProblemDeclaration (probName ++ `reduced) redProbExpr false

      -- Call the solver on prob.reduced and get a point in E.
      let (coeffsData, sections) ← determineCoeffsFromExpr redProb
      trace[Meta.debug] "coeffsData: {coeffsData}"
      let solPointResponse ← Meta.conicSolverFromValues redProb coeffsData sections
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
          let solPointExpr ← Meta.exprFromSol redProb solPoint
          trace[Meta.debug] "solPointExpr: {solPointExpr}"

          let backwardMapFloat ← realToFloat <| ← whnf backwardMap
          let solPointExprFloat ← realToFloat solPointExpr

          let probSolPointFloat ← whnf <| mkAppN backwardMapFloat #[solPointExprFloat]
          trace[Meta.debug] "probSolPointFloat: {probSolPointFloat}"

          -- Add the solution point to the environment.
          addProblemDeclaration (probName ++ `solution) probSolPointFloat true

          -- Also add value of optimal point.
          let probSolValue := mkApp redProb.objFun solPointExpr
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
