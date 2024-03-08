import Lean

/-!
Custom error messages.
-/

section Syntax

/-- Throws an error coming from parsing the optimization problem using the custom syntax defined in
`CvxLean/Syntax/Minimization.lean`. -/
syntax "throwParserError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwParserError $msg:interpolatedStr) => `(throwError ("Parser error: " ++ (m! $msg)))
  | `(throwParserError $msg:term) => `(throwError ("Parser error: " ++ $msg))

end Syntax

section Meta

/-- Throws an error coming from the tactic builder machinery (`CvxLean/Meta/TacticBuilder.lean`). -/
syntax "throwTacticBuilderError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwTacticBuilderError $msg:interpolatedStr) =>
      `(throwError ("Tactic builder error: " ++ (m! $msg)))
  | `(throwTacticBuilderError $msg:term) => `(throwError ("Tactic builder error: " ++ $msg))

end Meta

section BasicTactics

/-- Throws an error coming from the `clean_up_comp` tactic. -/
syntax "throwCleanUpCompError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwCleanUpCompError $msg:interpolatedStr) =>
      `(throwError ("`clean_up_comp` error: " ++ (m! $msg)))
  | `(throwCleanUpCompError $msg:term) => `(throwError ("`clean_up_comp` error: " ++ $msg))

/-- Throws an error coming from the `change_of_variables` tactic. -/
syntax "throwChangeOfVariablesError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwChangeOfVariablesError $msg:interpolatedStr) =>
      `(throwError ("`change_of_variables` error: " ++ (m! $msg)))
  | `(throwChangeOfVariablesError $msg:term) =>
      `(throwError ("`change_of_variables` error: " ++ $msg))

/-- Throws an error coming from the `conv_opt` tactic. -/
syntax "throwConvOptError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwConvOptError $msg:interpolatedStr) => `(throwError ("`conv_opt` error: " ++ (m! $msg)))
  | `(throwConvOptError $msg:term) => `(throwError ("`conv_opt` error: " ++ $msg))

/-- Throws an error coming from the `conv_obj` tactic. -/
syntax "throwConvObjError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwConvObjError $msg:interpolatedStr) => `(throwError ("`conv_obj` error: " ++ (m! $msg)))
  | `(throwConvObjError $msg:term) => `(throwError ("`conv_obj` error: " ++ $msg))

/-- Throws an error coming from the `conv_constr` tactic. -/
syntax "throwConvConstrError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwConvConstrError $msg:interpolatedStr) =>
      `(throwError ("`conv_constr` error: " ++ (m! $msg)))
  | `(throwConvConstrError $msg:term) => `(throwError ("`conv_constr` error: " ++ $msg))

/-- Throws an error coming from the `remove_constrs` tactic. -/
syntax "throwRemoveConstrError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRemoveConstrError $msg:interpolatedStr) =>
      `(throwError ("`remove_constr` error: " ++ (m! $msg)))
  | `(throwRemoveConstrError $msg:term) => `(throwError ("`remove_constr` error: " ++ $msg))

/-- Throws an error coming from the `remove_trivial_constrs` tactic. -/
syntax "throwRemoveTrivialConstrsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRemoveTrivialConstrsError $msg:interpolatedStr) =>
      `(throwError ("`remove_trivial_constrs` error: " ++ (m! $msg)))
  | `(throwRemoveTrivialConstrsError $msg:term) =>
      `(throwError ("`remove_trivial_constrs` error: " ++ $msg))

/-- Throws an error coming from the `rename_constrs` tactic. -/
syntax "throwRenameConstrsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRenameConstrsError $msg:interpolatedStr) =>
      `(throwError ("`rename_constrs` error: " ++ (m! $msg)))
  | `(throwRenameConstrsError $msg:term) => `(throwError ("`rename_constrs` error: " ++ $msg))

/-- Throws an error coming from the `rename_vars` tactic. -/
syntax "throwRenameVarsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRenameVarsError $msg:interpolatedStr) =>
      `(throwError ("`rename_vars` error: " ++ (m! $msg)))
  | `(throwRenameVarsError $msg:term) => `(throwError ("`rename_vars` error: " ++ $msg))

/-- Throws an error coming from the `reorder_constrs` tactic. -/
syntax "throwReorderConstrsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwReorderConstrsError $msg:interpolatedStr) =>
      `(throwError ("`reorder_constrs` error: " ++ (m! $msg)))
  | `(throwReorderConstrsError $msg:term) => `(throwError ("`reorder_constrs` error: " ++ $msg))

/-- Throws an error coming from the `rw_constr` tactic. -/
syntax "throwRwConstrError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRwConstrError $msg:interpolatedStr) => `(throwError ("`rw_constr` error: " ++ (m! $msg)))
  | `(throwRwConstrError $msg:term) => `(throwError ("`rw_constr` error: " ++ $msg))

/-- Throws an error coming from the `rw_obj` tactic. -/
syntax "throwRwObjError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRwObjError $msg:interpolatedStr) => `(throwError ("`rw_obj` error: " ++ (m! $msg)))
  | `(throwRwObjError $msg:term) => `(throwError ("`rw_obj` error: " ++ $msg))

end BasicTactics

section PreDCP

/-- Throws an error coming from the `pre_dcp` tactic or any of the auxiliary functions. -/
syntax "throwPreDCPError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwPreDCPError $msg:interpolatedStr) => `(throwError ("`pre_dcp` error: " ++ (m! $msg)))
  | `(throwPreDCPError $msg:term) => `(throwError ("`pre_dcp` error: " ++ $msg))

end PreDCP

section DCP

/-- Throws an error coming from the `declare_atom` command. -/
syntax "throwAtomDeclarationError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwAtomDeclarationError $msg:interpolatedStr) =>
      `(throwError ("`declare_atom` error: " ++ (m! $msg)))
  | `(throwAtomDeclarationError $msg:term) => `(throwError ("`declare_atom` error: " ++ $msg))

/-- Throws an error coming from the `dcp` tactic or any of the auxiliary functions. -/
syntax "throwDCPError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwDCPError $msg:interpolatedStr) => `(throwError ("`dcp` error: " ++ (m! $msg)))
  | `(throwDCPError $msg:term) => `(throwError ("`dcp` error: " ++ $msg))

end DCP

section Solve

/-- Throws an error coming from the coefficient extraction procedure
(`CvxLean/Command/Solve/Float/Coeffs.lean`). -/
syntax "throwCoeffsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwCoeffsError $msg:interpolatedStr) =>
      `(throwError ("Coefficient extraction error: " ++ (m! $msg)))
  | `(throwCoeffsError $msg:term) => `(throwError ("Coefficient extraction error: " ++ $msg))

/-- Throws an error coming from the real-to-float procedure
(`CvxLean/Command/Solve/Float/RealToFloatCmd.lean`). -/
syntax "throwRealToFloatError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRealToFloatError $msg:interpolatedStr) =>
      `(throwError ("Real-to-float error: " ++ (m! $msg)))
  | `(throwRealToFloatError $msg:term) => `(throwError ("Real-to-float error: " ++ $msg))

/-- Throws an error coming from the `solve` command. -/
syntax "throwSolveError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwSolveError $msg:interpolatedStr) => `(throwError ("`solve` error: " ++ (m! $msg)))
  | `(throwSolveError $msg:term) => `(throwError ("`solve` error: " ++ $msg))

end Solve

section Equivalence

/-- Throws an error coming from the `equivalence` command. -/
syntax "throwEquivalenceError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwEquivalenceError $msg:interpolatedStr) =>
      `(throwError ("`equivalence` error: " ++ (m! $msg)))
  | `(throwEquivalenceError $msg:term) => `(throwError ("`equivalence` error: " ++ $msg))

end Equivalence

section Reduction

/-- Throws an error coming from the `reduction` command. -/
syntax "throwReductionError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwReductionError $msg:interpolatedStr) =>
      `(throwError ("`reduction` error: " ++ (m! $msg)))
  | `(throwReductionError $msg:term) => `(throwError ("`reduction` error: " ++ $msg))

section Relaxation

/-- Throws an error coming from the `relaxation` command. -/
syntax "throwRelaxationError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRelaxationError $msg:interpolatedStr) =>
      `(throwError ("`relaxation` error: " ++ (m! $msg)))
  | `(throwRelaxationError $msg:term) => `(throwError ("`relaxation` error: " ++ $msg))

end Relaxation
