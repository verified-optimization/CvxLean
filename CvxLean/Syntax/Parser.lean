import Lean 

namespace CvxLean

open Lean

namespace Parser

open Lean.Parser

def minimizationVar : Parser := 
  leading_parser ((ident <|> Term.bracketedBinder) >> ppSpace)

def constraint : Parser := 
  leading_parser (ppLine >> checkColGe >> ppGroup (Term.binderIdent >> " : " >> termParser))

def constraints : Parser := 
  leading_parser manyIndent constraint

def minOrMax := 
  leading_parser "minimize " <|> "maximize "

end Parser

section Syntax

open Parser Lean.Parser

scoped syntax (name := optimization)
  ppGroup("optimization " minimizationVar*)
  ppLine ppGroup(minOrMax term)
  (ppLine ppGroup("subject to " constraints))?
  ppLine
  : term
  
-- By using the "scoped" keyword, the syntax only works when opening the CvxLean
-- namespace, but when the namespace is not open, "optimization", "minimize",
-- "maximize", and "subject to" will not be keywords and can be used as names.

end Syntax

end CvxLean
