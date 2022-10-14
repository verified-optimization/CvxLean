import Lean

namespace CvxLean

namespace Parser

open Lean.Parser

def implementationObjective := leading_parser withPosition $
  nonReservedSymbol "implementationObjective" >> 
  checkColGt "indented term" >> termParser

def solutionEqualsAtom := leading_parser withPosition $
  nonReservedSymbol "solutionEqualsAtom" >> 
  checkColGt "indented term" >> termParser

def optimality := leading_parser withPosition $
  nonReservedSymbol "optimality" >> 
  checkColGt "indented term" >> termParser

def homogenity := leading_parser withPosition $
  nonReservedSymbol "homogenity" >> 
  checkColGt "indented term" >> termParser

def additivity := leading_parser withPosition $
  nonReservedSymbol "additivity" >> 
  checkColGt "indented term" >> termParser

end Parser

declare_syntax_cat id_with_type
syntax "(" ident ":" term ")" : id_with_type

declare_syntax_cat id_with_def
syntax "(" ident ":=" term ")" : id_with_def

declare_syntax_cat arg_kind
syntax "+" : arg_kind
syntax "-" : arg_kind
syntax "?" : arg_kind
syntax "&" : arg_kind

declare_syntax_cat arg_with_kind
syntax "(" ident ":" term ")" arg_kind : arg_with_kind

syntax (name:=atomCommand) 
  "declare_atom" ident "[" ident "]" arg_with_kind* ":" term ":="
  &"vconditions" id_with_type*
  &"implementationVars" id_with_type*
  Parser.implementationObjective
  &"implementationConstraints" id_with_type*
  &"solution" id_with_def*
  Parser.solutionEqualsAtom
  &"feasibility" id_with_type*
  Parser.optimality
  &"vconditionElimination" id_with_type* : command

syntax (name:=affineAtomCommand) 
  "declare_atom" ident "[" "affine" "]" arg_with_kind* ":" term ":="
  &"bconditions" id_with_type*
  Parser.homogenity
  Parser.additivity 
  Parser.optimality : command

syntax (name:=coneAtomCommand) 
  "declare_atom" ident "[" "cone" "]" arg_with_kind* ":" term ":="
  Parser.optimality : command

end CvxLean



