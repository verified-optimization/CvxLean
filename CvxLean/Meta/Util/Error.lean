import Lean

/-!
Custom error messages.
-/

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
