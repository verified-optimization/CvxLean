import Lean.Data.Parsec
import Lean.Data.Json.Parser

/-!
# Solution format definition and parser

See <https://docs.mosek.com/latest/toolbox/sol-format.html>. 
-/ 

namespace Sol

/-- Stores general information about the solution, crucially the optimality 
status of the problem and the attained values. -/
structure Summary where
  name            : String
  problemStatus   : String
  solutionStatus  : String
  objectiveName   : String
  primalObjective : Float
  dualObjective   : Float

namespace Summary 

instance : ToString Summary where 
  toString s :=
    s!"NAME             : {s.name} \n" ++ 
    s!"PROBLEM STATUS   : {s.problemStatus} \n" ++
    s!"SOLUTION STATUS  : {s.solutionStatus} \n" ++
    s!"OBJECTIVE NAME   : {s.objectiveName} \n" ++
    s!"PRIMAL OBJECTIVE : {s.primalObjective} \n" ++
    s!"DUAL OBJECTIVE   : {s.dualObjective} \n"

end Summary

/-- Variable status. Following MOSEK's documentation:
UN : Unknown status.
BS : Basic. Not at limit, adjusted to satisfy the constraints.
SB : Superbasic. Not at limit, adjusted to minimize or maximize the objective.
LL : At the lower limit (bound).
UL : At the upper limit (bound).
EQ : Lower limit is identical to upper limit.
** : Infeasible i.e. the lower limit is greater than the upper limit. -/
inductive StatusKey
| UN | BS | SB | LL | UL | EQ | IN

namespace StatusKey

instance : ToString StatusKey where 
  toString 
  | StatusKey.UN => "UN"
  | StatusKey.BS => "BS"
  | StatusKey.SB => "SB"
  | StatusKey.LL => "LL"
  | StatusKey.UL => "UL"
  | StatusKey.EQ => "EQ"
  | _            => "**"

end StatusKey

/-- Value of an optimization constraint. -/
structure Constraint where
  index      : Nat
  name       : String
  status     : StatusKey
  activity   : Float
  lowerLimit : Option Float
  upperLimit : Option Float
  dualLower  : Option Float
  dualUpper  : Option Float

namespace Constraint

instance : ToString Constraint where 
  toString c :=
    s!"{c.index} | " ++ 
    s!"{c.name} | " ++
    s!"{c.status} | " ++
    s!"{c.activity} | " ++
    s!"{c.lowerLimit} | " ++
    s!"{c.upperLimit} | " ++
    s!"{c.dualLower} | " ++
    s!"{c.dualUpper}"

end Constraint

/-- Value of an optimization variable. -/
structure Variable extends Constraint where
  conicDual : Option Float

namespace Variable

instance : ToString Variable where 
  toString v := 
    (toString v.toConstraint) ++ (s!" | {v.conicDual}")

end Variable

/-- Value of an entry of and symmetric matrix optimization variable. -/
structure SymmMatrixVariable where
  index  : Nat
  name   : String
  I      : Nat
  J      : Nat
  primal : Option Float
  dual   : Option Float

namespace SymmMatrixVariable

instance : ToString SymmMatrixVariable where 
  toString smv := 
    s!"{smv.index} | " ++ 
    s!"{smv.name} | " ++
    s!"{smv.I} | " ++
    s!"{smv.J} | " ++
    s!"{smv.primal} | " ++
    s!"{smv.dual}"

end SymmMatrixVariable

/-- All the data in MOSEK's solution file format. -/
structure Result where
  summary        : Summary
  constraints    : List Constraint
  vars           : List Variable
  symmMatrixVars : List SymmMatrixVariable

namespace Result

instance : ToString Result where
  toString res :=
    (toString res.summary) ++ "\n" ++ 
    "CONSTRAINTS \n" ++
    "INDEX | NAME | AT | ACTIVITY | LOWER LIMIT | UPPER LIMIT | DUAL LOWER | DUAL UPPER \n" ++
    (res.constraints.foldl (fun acc s => acc ++ (toString s) ++ "\n") "") ++ "\n" ++ 
    "VARIABLES \n" ++
    "INDEX | NAME | AT | ACTIVITY | LOWER LIMIT | UPPER LIMIT | DUAL LOWER | DUAL UPPER | CONIC DUAL \n" ++
    (res.vars.foldl (fun acc s => acc ++ (toString s) ++ "\n") "") ++ "\n" ++ 
    "SYMMETRIC MATRIX VARIABLES \n" ++ 
    "INDEX | NAME | I | J | PRIMAL | DUAL \n" ++ 
    (res.symmMatrixVars.foldl (fun acc s => acc ++ (toString s) ++ "\n") "") ++ "\n"

end Result

/-- Either a full result or a MOSEK error code. -/
inductive Response
| success (res : Result) : Response 
| failure (code : Nat)   : Response 

namespace Response

instance : ToString Response where
  toString 
  | success res  => toString res
  | failure code => s!"MOSEK failed with code {code}."

end Response

namespace Parser 

open Lean Parsec

/-- In the solution format, a line ends with some whitespaces or is the end of
the file. -/
private def endOfLine : Parsec Unit := 
  ws <|> (skipChar '\n' <|> eof)

/-- Parse only valid characters. -/
private def char : Parsec Char :=
  asciiLetter <|> hexDigit <|> pchar '_' <|> fail "Invalid character."

/-- Parse string containing only valid characters as in `char`. -/
private def string : Parsec String := 
  many1Chars char

/-- Parse a `Nat` using the `JsonNumber` parser. -/
private def nat : Parsec Nat :=
  Json.Parser.natMaybeZero

/-- Parse a `Float` using the `JsonNumber` parser. -/
private def float : Parsec Float := fun it₁ =>
  match Json.Parser.num it₁ with
  | ParseResult.success it₂ res =>
    let f := Float.ofScientific res.mantissa.toNat true res.exponent
    ParseResult.success it₂ (if res.mantissa < 0 then -f else f)
  | ParseResult.error it₂ err => ParseResult.error it₂ err

/-- Use `float` or return none if the string is `"NONE"`. -/
private def optionFloat : Parsec (Option Float) := 
  (some <$> float) <|> (skipString "NONE" *> pure none)

section Summary

/-- Skip the beginning of a summary line. -/
private def summaryIdentifier (id : String) : Parsec Unit := 
  skipString id *> ws *> skipChar ':' *> ws

/-- Generic function to parse summary lines. -/
private def summaryLine (id : String) (p : Parsec α) : Parsec α :=
  summaryIdentifier id *> p <* endOfLine 

/-- Specialize `summaryLine` to strings. -/
private def stringSummaryLine (id : String) : Parsec String := 
  summaryLine id string

/-- Specialize `summaryLine` to floats. -/
private def floatSummaryLine (id : String) : Parsec Float := 
  summaryLine id float

/-- Parse the whole `Sol.summary` section. -/
private def summary : Parsec Summary :=
  Summary.mk <$> 
  stringSummaryLine "NAME"             <*> 
  stringSummaryLine "PROBLEM STATUS"   <*> 
  stringSummaryLine "SOLUTION STATUS"  <*> 
  stringSummaryLine "OBJECTIVE NAME"   <*> 
  floatSummaryLine  "PRIMAL OBJECTIVE" <*> 
  floatSummaryLine  "DUAL OBJECTIVE"   <* endOfLine

end Summary 

section Constraints 

/-- Skip the title in the constraints section. -/
private def constraintsTitle : Parsec Unit := 
  skipString "CONSTRAINTS" <* endOfLine

/-- Skip the headers in the constraints section. -/
private def constraintsHeaders : Parsec Unit := 
  skipString "INDEX"       <* ws <* 
  skipString "NAME"        <* ws <* 
  skipString "AT"          <* ws <* 
  skipString "ACTIVITY"    <* ws <*
  skipString "LOWER LIMIT" <* ws <*
  skipString "UPPER LIMIT" <* ws <*
  skipString "DUAL LOWER"  <* ws <*
  skipString "DUAL UPPER"  <* endOfLine

/-- Parse a `StatusKey`. -/
private def statusKey : Parsec StatusKey := 
  (skipString "UN" *> pure StatusKey.UN) <|>
  (skipString "BS" *> pure StatusKey.BS) <|>
  (skipString "SB" *> pure StatusKey.SB) <|>
  (skipString "LL" *> pure StatusKey.LL) <|>
  (skipString "UL" *> pure StatusKey.UL) <|>
  (skipString "EQ" *> pure StatusKey.EQ) <|>
  (skipString "**" *> pure StatusKey.IN) <|>
  (fail "Invalid status key.")

/-- Generic function to parse constraint elements, handling whitespaces. -/
private def constraintElem (p : Parsec α) : Parsec α := 
  ws *> p

/-- Parse a `Constraint` line. -/
private def constraint : Parsec Constraint := 
  Constraint.mk <$> 
  constraintElem nat         <*> 
  constraintElem string      <*>
  constraintElem statusKey   <*> 
  constraintElem float       <*> 
  constraintElem optionFloat <*> 
  constraintElem optionFloat <*> 
  constraintElem optionFloat <*> 
  constraintElem optionFloat <* endOfLine

/-- Parse the whole `Sol.Result.constraints` section. -/
private def constraints : Parsec (List Constraint) := 
  constraintsTitle   *>
  constraintsHeaders *>
  Array.data <$> many constraint

end Constraints 

section Variables

/-- Skip the title in the variables section. -/
private def varsTitle : Parsec Unit := 
  skipString "VARIABLES" <* endOfLine

/-- Skip the headers in the variables section. Handle CONIC DUAL case. -/
private def varsHeaders : Parsec Unit := 
  constraintsHeaders <* 
  (skipString "CONIC DUAL" <|> pure ()) <* endOfLine

/-- Parse a `Variable` line. -/
private def var : Parsec Variable := 
  Variable.mk <$> constraint <*> 
  (constraintElem optionFloat <|> pure none) <* endOfLine

/-- Parse the whole `Sol.Result.variables` section. -/
private def vars : Parsec (List Variable) := 
  varsTitle   *>
  varsHeaders *>
  Array.data <$> many var

end Variables 

section SymmMatrixVariable

/-- Skip the title in the symmetric matrix variables section. -/
private def symmMatrixVarsTitle : Parsec Unit := 
  skipString "SYMMETRIC MATRIX VARIABLES" <* endOfLine

/-- Skip the headers in the symmetric matrix variables section. -/
private def symmMatrixVarsHeaders : Parsec Unit := 
  skipString "INDEX"  <* ws <* 
  skipString "NAME"   <* ws <* 
  skipString "I"      <* ws <* 
  skipString "J"      <* ws <*
  skipString "PRIMAL" <* ws <*
  skipString "DUAL"   <* endOfLine

/-- Parse a `SymmMatrixVariable` line. -/
private def symmMatrixVar : Parsec SymmMatrixVariable := 
  SymmMatrixVariable.mk <$> 
  constraintElem nat         <*> 
  constraintElem string      <*> 
  constraintElem nat         <*> 
  constraintElem nat         <*> 
  constraintElem optionFloat <*> 
  constraintElem optionFloat <* endOfLine

/-- Parse the whole `Sol.Result.symmMatrixVariables` section. -/
private def symmMatrixVars : Parsec (List SymmMatrixVariable) := 
  symmMatrixVarsTitle   *>
  symmMatrixVarsHeaders *>
  Array.data <$> many symmMatrixVar

end SymmMatrixVariable

/-- Parse the whole `Sol.Result` object. -/
def result : Parsec Result := 
  Result.mk <$>
  summary        <* ws <*>
  constraints    <* ws <*>
  vars           <* ws <*>
  symmMatrixVars <* endOfLine

/-- Parse using `result` and handle errors. -/
def parse (s : String) : Except String Result :=
  match result s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => 
    Except.error s!"Error at offset {it.i.byteIdx}: {err}."

end Parser 

end Sol
