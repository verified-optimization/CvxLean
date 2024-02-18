import CvxLean.Tactic.Basic.ConvOpt

/-!
# Simple tactic to normalize numerical constants

Applying `norm_num` directly is possible, but makes us lose control over how the chain of relations
is built. By calling it in `conv` mode, we make sure that the normalization happens behind the
`Equivalence.ofEq` constructor, which ensures that we can always obtain a computable backward map,
as creating the map relies on simplifying the chain of relations.
-/

namespace CvxLean

open Lean Elab Meta Tactic

namespace Meta

def normNumOptBuilder : EquivalenceBuilder Unit :=
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
