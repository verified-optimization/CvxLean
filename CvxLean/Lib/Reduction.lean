import CvxLean.Lib.Equivalence

/-!
# Reduction

TODO
-/

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)

/-- TODO -/
structure Reduction where
  psi : E → D
  psi_optimality : ∀ x, q.optimal x → p.optimal (psi x)

namespace Reduction

variable {p q r}

notation p " ≽ " q => Reduction p q

def refl : p ≽ p :=
  { psi := id,
    psi_optimality := fun _ hy => hy }

def trans (R₁ : p ≽ q) (R₂ : q ≽ r) : p ≽ r :=
  { psi := R₁.psi ∘ R₂.psi,
    psi_optimality := fun x h => R₁.psi_optimality (R₂.psi x) (R₂.psi_optimality x h) }

instance : Trans (@Reduction D E R _) (@Reduction E F R _) (@Reduction D F R _) :=
  { trans := Reduction.trans }

def toBwd (R : p ≽ q) : Solution q → Solution p :=
  fun sol =>
    have ⟨feasibility, optimality⟩ := R.psi_optimality sol.point ⟨sol.feasibility, sol.optimality⟩;
    ⟨R.psi sol.point, feasibility, optimality⟩

def ofEquivalence (E : Equivalence p q) : p ≽ q :=
  { psi := E.psi,
    psi_optimality := E.psi_optimality }

instance : Trans (@Reduction D E R _) (@Equivalence E F R _) (@Reduction D F R _) :=
  { trans := fun R E => Reduction.trans R (ofEquivalence E) }

instance : Trans (@Equivalence D E R _) (@Reduction E F R _) (@Reduction D F R _) :=
  { trans := fun E R => Reduction.trans (ofEquivalence E) R }

-- TODO
-- All equivalences yield reductions. Build lemmas in meta? Is it useful to have them?

section Maps

def map_objFun {g : R → R} (h : ∀ {r s}, cs r → cs s → (g (f r) ≤ g (f s) ↔ f r ≤ f s)) :
    ⟨f, cs⟩ ≽ ⟨fun x => g (f x), cs⟩ :=
  ofEquivalence <| Equivalence.map_objFun h

noncomputable def map_objFun_log {f : D → ℝ} (h : ∀ x, cs x → f x > 0) :
    ⟨f, cs⟩ ≽ ⟨fun x => (Real.log (f x)), cs⟩ :=
  ofEquivalence <| Equivalence.map_objFun_log h

noncomputable def map_objFun_sq {f : D → ℝ} (h : ∀ x, cs x → f x ≥ 0) :
    ⟨f, cs⟩ ≽ ⟨fun x => (f x) ^ (2 : ℝ), cs⟩ :=
  ofEquivalence <| Equivalence.map_objFun_sq h

def map_domain {f : D → R} {cs : D → Prop} {fwd : D → E} {bwd : E → D}
    (h : ∀ x, cs x → bwd (fwd x) = x) :
    ⟨f, cs⟩ ≽ ⟨fun x => f (bwd x), (fun x => cs (bwd x))⟩ :=
  ofEquivalence <| Equivalence.map_domain h

end Maps

section Rewrites

variable {f g : D → R}
variable {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : D → Prop}
variable {c1' c2' c3' c4' c5' c6' c7' c8' c9' c10' : D → Prop}
variable {cs cs' : D → Prop}

def rewrite_objective (hrw : ∀ x, cs x → f x = g x) : ⟨f, cs⟩ ≽ ⟨g, cs⟩ :=
  ofEquivalence <| Equivalence.rewrite_objective hrw

def rewrite_constraints (hrw : ∀ x, cs x ↔ cs' x) : ⟨f, [[cs]]⟩ ≽ ⟨f, [[cs']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraints hrw

def rewrite_constraint_1 (hrw : ∀ x, cs x → (c1 x ↔ c1' x)) : ⟨f, [[c1, cs]]⟩ ≽ ⟨f, [[c1', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_1 hrw

def rewrite_constraint_1_last (hrw : ∀ x, c1 x ↔ c1' x) : ⟨f, [[c1]]⟩ ≽ ⟨f, [[c1']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_1_last hrw

def rewrite_constraint_2 (hrw : ∀ x, c1 x → cs x → (c2 x ↔ c2' x)) :
    ⟨f, [[c1, c2, cs]]⟩ ≽ ⟨f, [[c1, c2', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_2 hrw

def rewrite_constraint_2_last (hrw : ∀ x, c1 x → (c2 x ↔ c2' x)) :
    ⟨f, [[c1, c2]]⟩ ≽ ⟨f, [[c1, c2']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_2_last hrw

def rewrite_constraint_3 (hrw : ∀ x, c1 x → c2 x → cs x → (c3 x ↔ c3' x)) :
    ⟨f, [[c1, c2, c3, cs]]⟩ ≽ ⟨f, [[c1, c2, c3', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_3 hrw

def rewrite_constraint_3_last (hrw : ∀ x, c1 x → c2 x → (c3 x ↔ c3' x)) :
    ⟨f, [[c1, c2, c3]]⟩ ≽ ⟨f, [[c1, c2, c3']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_3_last hrw

def rewrite_constraint_4 (hrw : ∀ x, c1 x → c2 x → c3 x → cs x → (c4 x ↔ c4' x)) :
    ⟨f, [[c1, c2, c3, c4, cs]]⟩ ≽ ⟨f, [[c1, c2, c3, c4', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_4 hrw

def rewrite_constraint_4_last (hrw : ∀ x, c1 x → c2 x → c3 x → (c4 x ↔ c4' x)) :
    ⟨f, [[c1, c2, c3, c4]]⟩ ≽ ⟨f, [[c1, c2, c3, c4']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_4_last hrw

def rewrite_constraint_5 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → cs x → (c5 x ↔ c5' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, cs]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_5 hrw

def rewrite_constraint_5_last (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → (c5 x ↔ c5' x)) :
    ⟨f, [[c1, c2, c3, c4, c5]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_5_last hrw

def rewrite_constraint_6 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → cs x → (c6 x ↔ c6' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, cs]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5, c6', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_6 hrw

def rewrite_constraint_6_last (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → (c6 x ↔ c6' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5, c6']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_6_last hrw

def rewrite_constraint_7
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → cs x → (c7 x ↔ c7' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, cs]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5, c6, c7', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_7 hrw

def rewrite_constraint_7_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → (c7 x ↔ c7' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5, c6, c7']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_7_last hrw

def rewrite_constraint_8
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → cs x → (c8 x ↔ c8' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, cs]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_8 hrw

def rewrite_constraint_8_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → (c8 x ↔ c8' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8]]⟩ ≽ ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_8_last hrw

def rewrite_constraint_9
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → cs x → (c9 x ↔ c9' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, cs]]⟩ ≽
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_9 hrw

def rewrite_constraint_9_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → (c9 x ↔ c9' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9]]⟩ ≽
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_9_last hrw

def rewrite_constraint_10
    (hrw :
      ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → cs x → (c10 x ↔ c10' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, cs]]⟩ ≽
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10', cs]]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_10 hrw

def rewrite_constraint_10_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → (c10 x ↔ c10' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]]⟩ ≽
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10']]⟩ :=
  ofEquivalence <| Equivalence.rewrite_constraint_10_last hrw

end Rewrites

section Other

-- TODO: from equiv.

end Other

end Reduction

end Minimization
