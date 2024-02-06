import Lean

/-!
Attributes for lemmas that make strong equivalences, equivalences, reductions, and relaxations. By
tagging them, we can easily retrieve all the lemmas for a certain relation.
-/

open Lean Meta

initialize strongEquivThmExtension : SimpExtension ←
  registerSimpAttr `strong_equiv "Strong equivalence theorem."

initialize equivThmExtension : SimpExtension ←
  registerSimpAttr `equiv "Equivalence theorem."

initialize redThmExtension : SimpExtension ←
  registerSimpAttr `red "Reduction theorem."

initialize relThmExtension : SimpExtension ←
  registerSimpAttr `rel "Relaxation theorem."
