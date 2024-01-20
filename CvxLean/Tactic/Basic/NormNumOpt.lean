import CvxLean.Tactic.Basic.ConvOpt

/-!
# Simple tactic to

This is used, for example, in `pre_dcp` so that numbers are in the right format.
-/

namespace CvxLean

open Lean Elab Meta Tactic

namespace Meta

def normNumOptBuilder : EquivalenceBuilder :=
  Conv.convertOpt (fullProb := true) (convTac := Mathlib.Tactic.elabNormNum1Conv mkNullNode)

end Meta

namespace Tactic

/-- Apply `norm_num1` in conv mode. -/
syntax (name := normNumOpt) "norm_num_opt" : tactic

@[tactic normNumOpt]
def evalNormNumOpt : Tactic := fun stx => match stx with
  | `(tactic| norm_num_opt) => withMainContext do
      normNumOptBuilder.toTactic
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax


end Tactic

end CvxLean
