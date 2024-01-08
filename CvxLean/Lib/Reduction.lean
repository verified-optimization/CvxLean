import CvxLean.Lib.Equivalence

/-!
# Reduction
-/

namespace Minimization

variable {D E R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R)

abbrev Reduction := Solution q → Solution p

namespace Reduction

notation p " ≽ " q => Reduction p q

def map_objFun' {g : R → R}
    (h : ∀ {r s}, cs r → cs s → (g (f r) ≤ g (f s) ↔ f r ≤ f s)) :
    ⟨f, cs⟩ ≽ ⟨fun x => g (f x), cs⟩ :=
  Equivalence.map_objFun h |>.toBwd

section Maps

end Maps


section Rewrites

end Rewrites

end Reduction

end Minimization
