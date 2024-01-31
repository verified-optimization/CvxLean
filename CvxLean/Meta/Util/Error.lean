import Lean

/-!
Custom error messages.
-/

syntax "throwCoeffsError " (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwCoeffsError $msg:interpolatedStr) => `(throwError ("`coeffs` error: " ++ (m! $msg)))
