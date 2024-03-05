import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Math.Data.Vec
import CvxLean.Lib.Math.Data.Matrix
import CvxLean.Lib.Math.CovarianceEstimation
import CvxLean.Lib.Math.LogDet
import CvxLean.Lib.Cones.All
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Error
import CvxLean.Meta.Minimization
import CvxLean.Syntax.OptimizationParam
import CvxLean.Command.Solve.Float.RealToFloatExt

/-!
# Conversion of Real to Float (command)

We define the `realToFloat` function to go from real `Expr`s to float `Expr`s as well as the
`add_real_to_float` command to add new translations and the `#real_to_float` command to test the
translation.
-/

namespace CvxLean

open Lean Expr Elab Meta Command Term

syntax (name := addRealToFloatCommand)
  "add_real_to_float" Lean.Parser.Term.funBinder* ":" term ":=" term : command

/-- Traverse expression recursively and if a match is found in the real-to-float library return the
float version. The "correctness" of this function depends on the translations defined in the
library. -/
partial def realToFloat (e : Expr) : MetaM Expr := do
  let e ← e.removeMData
  let discrTree ← getRealToFloatDiscrTree
  let translations ← discrTree.getMatch e
  for translation in translations do
    let (mvars, _, pattern) ← lambdaMetaTelescope translation.real
    if ← isDefEq pattern e then
      -- TODO: Search for conditions.
      let args ← mvars.mapM instantiateMVars
      return mkAppNBeta translation.float args
    else
      throwRealToFloatError "no match for \n{pattern} \n{e}"
  match e with
  | Expr.app a b => return mkApp (← realToFloat a) (← realToFloat b)
  | Expr.lam n ty b d => do
      withLocalDecl n d (← realToFloat ty) fun fvar => do
        let b := b.instantiate1 fvar
        let bF ← realToFloat b
        mkLambdaFVars #[fvar] bF
  | Expr.forallE n ty b d => do
      withLocalDecl n d (← realToFloat ty) fun fvar => do
        let b := b.instantiate1 fvar
        let bF ← realToFloat b
        mkForallFVars #[fvar] bF
  | Expr.mdata m e => return mkMData m (← realToFloat e)
  | Expr.letE n ty t b _ => return mkLet n (← realToFloat ty) (← realToFloat t) (← realToFloat b)
  | Expr.proj typeName idx struct => return mkProj typeName idx (← realToFloat struct)
  | e@(Expr.const n _) => do
      if ← isOptimizationParam n then
        let paramExpr ← getOptimizationParamExpr n e
        let paramExprF ← realToFloat paramExpr
        -- Also add the float the definition of the parameter to the the environment if it is not
        -- there already.
        try
          let nF := n ++ `float
          if !(← getEnv).contains nF then
            simpleAddAndCompileDefn nF paramExprF
        catch e =>
          throwRealToFloatError "failed to create `{n}.float`.\n{e.toMessageData}"
        return paramExprF
      else
        return e
  | _ => return e

/-- The `add_real_to_float` command, which simply adds the user-defined expressions to the
environment extension. -/
@[command_elab addRealToFloatCommand]
def elabAddRealToFloatCommand : CommandElab
  | `(add_real_to_float : $real := $float) =>
      liftTermElabM do
        let real ← elabTermAndSynthesize real.raw none
        let float ← elabTermAndSynthesize float.raw none
        addRealToFloatData { real := real, float := float }
  | _ => throwUnsupportedSyntax

macro_rules
| `(add_real_to_float $idents:funBinder* : $real := $float) => do
  if idents.size != 0 then
    `(add_real_to_float : fun $idents:funBinder* => $real := fun $idents:funBinder* => $float)
  else
    Macro.throwUnsupported

syntax (name:=realToFloatCommand)
  "#real_to_float" term : command

/-- Transform the given expression to its float version and log the result. -/
@[command_elab realToFloatCommand]
unsafe def elabRealToFloatCommand : CommandElab
| `(#real_to_float $stx) =>
  liftTermElabM do
    let e ← elabTermAndSynthesize stx.raw none
    let res ← realToFloat e
    check res
    logInfo m!"{res}"
    if Expr.isConstOf (← inferType res) ``Float then
      let res ← Meta.evalExpr Float (mkConst ``Float) res
      logInfo m!"{res}"
| _ => throwUnsupportedSyntax

end CvxLean
