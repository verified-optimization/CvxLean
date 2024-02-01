import CvxLean.Tactic.DCP.AtomLibrary.All
import CvxLean.Command.Solve.Conic

/-!
# The `solve` command

Given a problem `p : Minimization D R` a user can call `solve p` to call an external solver and
obtain a result. If successful, three new definitions are added to the environment:
* `p.reduced : Minimization (D × E) R` is the problem in conic form.
* `p.status : String` is the status of the solution.
* `p.solution : D` is the solution to the problem.
* `p.value : R` is the value of the solution.
-/

namespace CvxLean

open Lean Meta Elab Term Command Minimization

/-- Get problem name. Used to add information about the solution to the environment. -/
def getProblemName (stx : Syntax) : MetaM Name := do
  -- TODO: Full name with parameters?
  let idStx :=
    match stx with
    | Syntax.ident _ _ _ _ => stx
    | Syntax.node _ _ args => args.getD 0 Syntax.missing
    | _ => Syntax.missing
  if ¬ idStx.getId.isStr then
    throwError "Invalid name for minimization problem: {idStx}."

  return idStx.getId

/-- Call DCP and get the problem in conic form as well as `ψ`, the backward map from the
equivalence. -/
def getReducedProblemAndBwdMap (prob : Expr) : MetaM (MinimizationExpr × Expr) := do
  let ogProb ← MinimizationExpr.fromExpr prob
  let (redProb, eqvProof) ← DCP.canonize ogProb
  let backwardMap ← mkAppM ``Minimization.Equivalence.psi #[eqvProof]
  return (redProb, backwardMap)

syntax (name := solve) "solve " term : command

/-- The `solve` command. It works as follows:
1. Reduce optimization problem to conic form.
2. Extract problem data using `determineCoeffsFromExpr`.
3. Obtain a solution using `solutionDataFromProblemData`, which calls an external solver.
4. Store the result in the enviroment. -/
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
      trace[CvxLean.debug] "Coeffs data:\n{coeffsData}"

      let solData ← solutionDataFromProblemData redProb coeffsData sections
      trace[CvxLean.debug] "Solution data:\n{solData}"

      -- Add status to the environment.
      simpleAddAndCompileDefn (probName ++ `status) (mkStrLit solData.status)

      -- TODO: For now, we are only handling this case.
      if solData.status != "PRIMAL_AND_DUAL_FEASIBLE" then
        pure ()

      -- Solution makes sense, handle the numerical solution.
      let solPointExpr ← exprFromSolutionData redProb solData
      trace[CvxLean.debug] "Solution point (reduced problem): {solPointExpr}"

      let backwardMapFloat ← realToFloat <| ← whnf backwardMap
      let solPointExprFloat ← realToFloat solPointExpr

      let probSolPointFloat ← whnf <| mkAppN backwardMapFloat #[solPointExprFloat]
      trace[CvxLean.debug] "Float solution point (original problem): {probSolPointFloat}"

      -- Add the solution point to the environment.
      simpleAddAndCompileDefn (probName ++ `solution) probSolPointFloat

      -- Also add value of optimal point.
      let probSolValue := mkApp redProb.objFun solPointExpr
      let probSolValueFloat ← realToFloat probSolValue
      check probSolValueFloat

      let mut probSolValueFloat := Expr.headBeta probSolValueFloat
      trace[CvxLean.debug] "Float problem value (original problem): {probSolValueFloat}"

      if probSolValueFloat.getAppFn.isConstOf `CvxLean.maximizeNeg then
        probSolValueFloat := probSolValueFloat.getAppArgs[2]!
      simpleAddAndCompileDefn (probName ++ `value) probSolValueFloat

      pure ()
  | _ => throwUnsupportedSyntax

end CvxLean
