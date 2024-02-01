import CvxLean.Tactic.DCP.AtomLibrary.All
import CvxLean.Command.Solve.Conic

/-!
# The `solve` command


-/

namespace CvxLean

open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta

open Minimization

/-- Get problem name. Used to add information about the solution to the environment. -/
def getProblemName (term : Syntax) : MetaM Lean.Name := do
  -- TODO: Full name with parameters.
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

syntax (name := solve) "solve " term : command

-- set_option maxHeartbeats 1000000

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

      simpleAddDefn (probName ++ `reduced) redProbExpr

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
          simpleAddAndCompileDefn (probName ++ `status) (mkStrLit solPoint.summary.problemStatus)

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
          simpleAddAndCompileDefn (probName ++ `solution) probSolPointFloat

          -- Also add value of optimal point.
          let probSolValue := mkApp redProb.objFun solPointExpr
          let probSolValueFloat ← realToFloat probSolValue
          trace[Meta.debug] "probSolValueFloat {probSolValueFloat}"
          check probSolValueFloat

          let mut probSolValueFloat := Expr.headBeta probSolValueFloat
          trace[Meta.debug] "probSolValueFloat reduced: {probSolValueFloat}"

          if probSolValueFloat.getAppFn.isConstOf `CvxLean.maximizeNeg then
            probSolValueFloat := probSolValueFloat.getAppArgs[2]!
          simpleAddAndCompileDefn (probName ++ `value) probSolValueFloat

          pure ()
  | _ => throwUnsupportedSyntax

end CvxLean
