import Lean

/-!
Custom error messages.
-/

syntax "throwCoeffsError " interpolatedStr(term) : term

macro_rules
  | `(throwCoeffsError $msg:interpolatedStr) =>
    `(throwError ("`coeffs` error: " ++ (m! $msg)))

syntax "throwRealToFloatError " interpolatedStr(term) : term

macro_rules
  | `(throwRealToFloatError $msg:interpolatedStr) =>
    `(throwError ("`real-to-float` error: " ++ (m! $msg)))
