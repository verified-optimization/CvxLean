import Lean

/-!
This file defines how to parse variables, constraints, objective functions and full optimization
problems. Syntax matching these definitions is elaborated in `Syntax/Minimization.lean`.
-/

namespace CvxLean

open Lean

namespace Parser

open Parser

def minimizationVar : Parser :=
  leading_parser ((ident <|> Term.bracketedBinder) >> ppSpace)

def letVar : Parser :=
  leading_parser "with " >> Term.letDecl >> ppSpace

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
  ppGroup("optimization " minimizationVar* letVar*)
    ppLine ppGroup(minOrMax term)
    (ppLine ppGroup("subject to " constraints))?
  ppLine : term

end Syntax

end CvxLean
