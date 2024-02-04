import Lean
import Mathlib.Tactic.NormNum
import CvxLean.Lib.Math.Data.Real

namespace CvxLean

open Lean Elab Meta Tactic

/-- Variant of `norm_num` used to get rid of the `OfScientific`s. -/
syntax (name := normNumCleanUp) "norm_num_clean_up" : tactic

macro_rules
  | `(tactic| norm_num_clean_up) =>
    `(tactic| repeat (conv in OfScientific.ofScientific _ _ _ => norm_num1))

/-- Variant of `norm_num` that simplifies powers. -/
syntax "norm_num_simp_pow" : tactic

macro_rules
  | `(tactic| norm_num_simp_pow) =>
    `(tactic| norm_num [Real.rpow_neg])

end CvxLean
