import CvxLean.Meta.Util.Error
import CvxLean.Command.Solve.Float.SolutionData
import CvxLean.Command.Solve.Mosek.Sol

/-!
Convert a `Sol.Result` to a `SolutionData`. The main definition is `Sol.toSolutionData`.
-/

namespace CvxLean.Sol

def Variable.toSimpleVarSol (v : Sol.Variable) : SimpleVarSol :=
  { name := v.name,
    value := v.activity }

def SymmMatrixVariable.toSimpleMatrixVarSol (v : Sol.SymmMatrixVariable) :
    SimpleMatrixVarSol :=
  { name := v.name,
    I := v.I,
    J := v.J,
    value := v.primal }

def Result.toSolutionData (sol : Sol.Result) : SolutionData :=
  { status := sol.summary.problemStatus,
    varsSols := sol.vars.map Variable.toSimpleVarSol,
    matrixVarsSols := sol.symmMatrixVars.map SymmMatrixVariable.toSimpleMatrixVarSol }

end CvxLean.Sol
