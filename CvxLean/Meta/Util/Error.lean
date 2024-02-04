import Lean

/-!
Custom error messages.
-/

syntax "throwRwConstrError" (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRwConstrError $msg:interpolatedStr) => `(throwError ("`rw_constr` error: " ++ (m! $msg)))
  | `(throwRwConstrError $msg:term) => `(throwError ("`rw_constr` error: " ++ $msg))

syntax "throwRwObjError" (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRwObjError $msg:interpolatedStr) => `(throwError ("`rw_obj` error: " ++ (m! $msg)))
  | `(throwRwObjError $msg:term) => `(throwError ("`rw_obj` error: " ++ $msg))

syntax "throwPreDCPError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwPreDCPError $msg:interpolatedStr) => `(throwError ("`pre_dcp` error: " ++ (m! $msg)))
  | `(throwPreDCPError $msg:term) => `(throwError ("`pre_dcp` error: " ++ $msg))

syntax "throwDCPError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwDCPError $msg:interpolatedStr) => `(throwError ("`dcp` error: " ++ (m! $msg)))
  | `(throwDCPError $msg:term) => `(throwError ("`dcp` error: " ++ $msg))

syntax "throwCoeffsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwCoeffsError $msg:interpolatedStr) => `(throwError ("`coeffs` error: " ++ (m! $msg)))
  | `(throwCoeffsError $msg:term) => `(throwError ("`coeffs` error: " ++ $msg))

syntax "throwRealToFloatError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRealToFloatError $msg:interpolatedStr) =>
    `(throwError ("`real-to-float` error: " ++ (m! $msg)))
  | `(throwRealToFloatError $msg:term) => `(throwError ("`real-to-float` error: " ++ $msg))

syntax "throwSolveError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwSolveError $msg:interpolatedStr) => `(throwError ("`solve` error: " ++ (m! $msg)))
  | `(throwSolveError $msg:term) => `(throwError ("`solve` error: " ++ $msg))

/-- Errors in the `equivalence` command. -/
syntax "throwEquivalenceError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwEquivalenceError $msg:interpolatedStr) =>
    `(throwError ("`equivalence` error: " ++ (m! $msg)))
  | `(throwEquivalenceError $msg:term) => `(throwError ("`equivalence` error: " ++ $msg))

/-- Errors in the `reduction` command. -/
syntax "throwReductionError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwReductionError $msg:interpolatedStr) =>
    `(throwError ("`reduction` error: " ++ (m! $msg)))
  | `(throwReductionError $msg:term) => `(throwError ("`reduction` error: " ++ $msg))

/-- Errors in the `relaxation` command. -/
syntax "throwRelaxationError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwRelaxationError $msg:interpolatedStr) =>
    `(throwError ("`relaxation` error: " ++ (m! $msg)))
  | `(throwRelaxationError $msg:term) => `(throwError ("`relaxation` error: " ++ $msg))
