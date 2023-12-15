import Lean
import Mathlib.Tactic.NormNum
import CvxLean.Lib.Math.Data.Real

namespace CvxLean

open Lean Elab Meta Tactic

/-- Variant of `norm_num` used to get rid of the `OfScientific`s. -/
def normNumCleanUp (useSimp : Bool) : TacticM Unit :=
  Mathlib.Meta.NormNum.elabNormNum mkNullNode mkNullNode (useSimp := useSimp)

syntax (name := norm_num_clean_up) "norm_num_clean_up" : tactic

@[tactic norm_num_clean_up]
def evalNormNumCleanUp : Tactic := fun stx => match stx with
  | `(tactic| norm_num_clean_up) => do
    normNumCleanUp (useSimp := false)
    saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax


/-- Variant of `norm_num` that simplifies powers. -/
syntax "norm_num_simp_pow" : tactic

macro_rules
  | `(tactic| norm_num_simp_pow) =>
    `(tactic| norm_num [Real.rpow_neg])

end CvxLean
