import Lean.Data.Parsec

/-!
# Solution format definition and parser

See <https://docs.mosek.com/latest/rmosek/sol-format.html>. 
-/ 

namespace Sol

/-- -/
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

/-- -/
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

/-- -/
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

/-- -/
structure Variable extends Constraint where
  conicDual : Option Float

namespace Variable

instance : ToString Variable where 
  toString v := 
    (toString v.toConstraint) ++ (s!" | {v.conicDual}")

end Variable

/- -/
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

/-- -/
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

/-- -/
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

-- TODO

end Parser 

end Sol
