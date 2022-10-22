import Lean
import Lean.Data.Json.Parser

import CvxLean.Tactic.Solver.Mosek.Sol

namespace Mosek

open Lean

-- Read basic data types.

def readFloat (s : String) 
  : MetaM Float :=
  match Json.Parser.num s.mkIterator with
  | Parsec.ParseResult.success _ res =>
      return Float.ofInt res.mantissa * (10 : Float) ^ - Float.ofNat res.exponent
  | Parsec.ParseResult.error it err  => 
      throwError s!"Float conversion error with {s}. Offset {repr it.i}: {err}"

def readOptionFloat (s : String) 
  : MetaM (Option Float) :=
  if s = "NONE" then 
    return none 
  else 
    return some (← readFloat s)

def readString (s : String) 
  : MetaM String :=
  return ⟨s.toList.filter (not $ Char.isWhitespace ·)⟩

def readLine (line : String) 
  : MetaM (List String) := do
  let elems ← (line.splitOn " ").mapM readString
  return elems.filter (not $ String.isEmpty ·)

-- Read summary.

def readSummaryLine (line : String) 
  : MetaM String := 
  let lineInfo := line.splitOn ":"
  if lineInfo.length != 2 then 
    throwError s!"Could not read summary line : {line}."
  else 
    readString (lineInfo.get! 1)
  
def readSummaryLines (lines : List String) 
  : MetaM Sol.Summary := do
  if lines.length != 6 then 
    throwError "Wrong number of summary parameters."
  else 
    let name ← readSummaryLine (lines.get! 0)
    let problemStatus ← readSummaryLine (lines.get! 1)
    let solutionStatus ← readSummaryLine (lines.get! 2)
    let objectiveName ← readSummaryLine (lines.get! 3)
    let primalObjective ← readSummaryLine (lines.get! 4) >>= readFloat
    let dualObjective ← readSummaryLine (lines.get! 5) >>= readFloat
    return (Sol.Summary.mk name problemStatus solutionStatus objectiveName primalObjective dualObjective)

-- Read status key.

def readStatusKey (s : String) 
  : MetaM (Sol.StatusKey) := 
  match s with 
  | "UN" => return Sol.StatusKey.UN 
  | "BS" => return Sol.StatusKey.BS 
  | "SB" => return Sol.StatusKey.SB 
  | "LL" => return Sol.StatusKey.LL 
  | "UL" => return Sol.StatusKey.UL 
  | "EQ" => return Sol.StatusKey.EQ 
  | "**" => return Sol.StatusKey.IN
  | _ => throwError s!"Unknown status key {s}."

-- Generic function to read lines for solution blocks.

def readSolLines (block : String) (lines : List String) (f : String → MetaM α) 
  : MetaM (List α) := do 
  if lines.length < 2 then 
    throwError s!"Wrong format for solution {block}s."
  else 
    let data := lines.drop 2 
    let mut res := [] 
    for line in data do
      if not line.isEmpty then
        let solConstraint ← f line 
        res := res.append [solConstraint]
    return res

-- Read constraints.

def readSolConstraintLineAux (lineInfo : List String) 
  : MetaM Sol.Constraint := do 
  if lineInfo.length != 8 then 
    throwError "Wrong number of solution constraint parameters."
  else 
    let index := (lineInfo.get! 0).toInt!.toNat
    let name := lineInfo.get! 1 
    let status ← readStatusKey (lineInfo.get! 2)
    let activity ← readFloat (lineInfo.get! 3)
    let lowerLimit ← readOptionFloat (lineInfo.get! 4)
    let upperLimit ← readOptionFloat (lineInfo.get! 5)
    let dualLower ← readOptionFloat (lineInfo.get! 6)
    let dualUpper ← readOptionFloat (lineInfo.get! 7)
    return (Sol.Constraint.mk index name status activity lowerLimit upperLimit dualLower dualUpper)

def readSolConstraintLine (line : String) 
  : MetaM Sol.Constraint := do 
  let lineInfo ← readLine line
  readSolConstraintLineAux lineInfo

def readSolConstraintLines (lines : List String) 
  : MetaM (List (Sol.Constraint)) :=
  readSolLines "constraint" lines readSolConstraintLine

-- Read variables.

def readSolVariableLine (line : String) 
  : MetaM Sol.Variable := do 
  let lineInfo ← readLine line
  if lineInfo.length == 8 then 
    let solConstraint ← readSolConstraintLineAux lineInfo
    return (Sol.Variable.mk solConstraint none)
  else if lineInfo.length == 9 then 
    let solConstraint ← readSolConstraintLineAux (lineInfo.dropLast)
    let conicDual ← readOptionFloat (lineInfo.get! (lineInfo.length - 1))
    return (Sol.Variable.mk solConstraint conicDual)
  else 
    throwError s!"Wrong number of solution variable parameters: {lineInfo.length}."

def readSolVariableLines (lines : List String) 
  : MetaM (List (Sol.Variable)) :=
  readSolLines "variable" lines readSolVariableLine

-- Read symmetric matrix variables.

def readSymmMatrixVariableLine (line : String) 
  : MetaM Sol.SymmMatrixVariable := do 
  let lineInfo ← readLine line
  if lineInfo.length != 6 then 
    throwError s!"Wrong number of solution symmetric matrix variable parameters: {lineInfo.length}."
  else 
    let index := (lineInfo.get! 0).toInt!.toNat 
    let name := lineInfo.get! 1 
    let I := (lineInfo.get! 2).toInt!.toNat 
    let J := (lineInfo.get! 3).toInt!.toNat 
    let primal ← readOptionFloat (lineInfo.get! 4)
    let dual ← readOptionFloat (lineInfo.get! 5)
    return (Sol.SymmMatrixVariable.mk index name I J primal dual)

def readSolSymmMatrixVariableLines (lines : List String) 
  : MetaM (List (Sol.SymmMatrixVariable)) :=
  readSolLines "symmetric matrix variable" lines readSymmMatrixVariableLine

-- Read solution.

def readOutput (path : String) 
  : MetaM Sol.Result := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.read
  let content ← IO.FS.Handle.readToEnd handle 
  let lines := String.splitOn content "\n\n"
  
  if lines.length < 3 ∨ lines.length > 4 then 
    throwError "Wrong solution format."
  else 
    let summaryStr := lines.get! 0
    let summaryLines := summaryStr.splitOn "\n"
    let solSummary ← readSummaryLines summaryLines
    
    let solConstraintStr := lines.get! 1 
    let solConstraintLines := solConstraintStr.splitOn "\n"
    let solConstraints ← readSolConstraintLines solConstraintLines

    let solVariableStr := lines.get! 2 
    let solVariableLines := solVariableStr.splitOn "\n"
    let solVariables ← readSolVariableLines solVariableLines

    if lines.length == 4 then
      let solSymmMatrixVariableStr := lines.get! 3 
      let solSymmMatrixVariableLines := solSymmMatrixVariableStr.splitOn "\n"
      let solSymmMatrixVariables ← readSolSymmMatrixVariableLines solSymmMatrixVariableLines
      return (Sol.Result.mk solSummary solConstraints solVariables solSymmMatrixVariables)
    else 
      return (Sol.Result.mk solSummary solConstraints solVariables [])

end Mosek
