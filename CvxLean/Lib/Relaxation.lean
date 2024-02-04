import CvxLean.Lib.Equivalence

/-!
# Relaxation of optimization problems

We define the notion of relaxation. It is a reflexive and transitive relation and it induces a
forward map between solutions. The idea is that solving the original problem is "as hard" as solving
the relaxed problem. A strong equivalence gives a relaxation.

## References

* <https://en.wikipedia.org/wiki/Relaxation_(approximation)>[RelaxationWiki]
-/

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)

/-- We read `Relaxation p q` as `p` relaxes to `q` or `q` is a relaxation of `p`. -/
structure Relaxation where
  phi : D → E
  phi_feasibility : ∀ x, p.feasible x → q.feasible (phi x)
  phi_optimality : ∀ x, p.feasible x → q.objFun (phi x) ≤ p.objFun x

namespace Relaxation

variable {p q r}

notation p " ≽' " q => Relaxation p q

@[rel]
def refl : p ≽' p :=
  { phi := id,
    phi_feasibility := fun _ h => h,
    phi_optimality := fun _ _ => le_refl _ }

@[rel]
def trans (Rx₁ : p ≽' q) (Rx₂ : q ≽' r) : p ≽' r :=
  { phi := Rx₂.phi ∘ Rx₁.phi,
    phi_feasibility := fun x h => Rx₂.phi_feasibility (Rx₁.phi x) (Rx₁.phi_feasibility x h),
    phi_optimality := fun x hx =>
      -- `h(φ₂(φ₁(x))) ≤ g(φ₁(x))`
      have h₁ := Rx₂.phi_optimality (Rx₁.phi x) (Rx₁.phi_feasibility x hx)
      -- `g(φ₁(x)) ≤ f(x)`
      have h₂ := Rx₁.phi_optimality x hx
      le_trans h₁ h₂ }

instance : Trans (@Relaxation D E R _) (@Relaxation E F R _) (@Relaxation D F R _) :=
  { trans := Relaxation.trans }

/-- First property in [RelaxationWiki]. -/
lemma feasible_and_bounded_of_feasible (Rx : p ≽' q) {x : D} (h_feas_x : p.feasible x) :
    q.feasible (Rx.phi x) ∧ q.objFun (Rx.phi x) ≤ p.objFun x :=
  ⟨Rx.phi_feasibility x h_feas_x, Rx.phi_optimality x h_feas_x⟩

/-- Second property in [RelaxationWiki]. NOTE: This does not use `Rx.phi_optimality`. -/
lemma induces_original_problem_optimality (Rx : p ≽' q) (phi_inv : E → D)
    (phi_left_inv : Function.LeftInverse Rx.phi phi_inv)
    (h_objFun : ∀ x, p.feasible x → p.objFun x = q.objFun (Rx.phi x)) {y : E}
    (h_opt_y : q.optimal y) (h_feas_y : p.feasible (phi_inv y)) : p.optimal (phi_inv y) := by
  refine ⟨h_feas_y, ?_⟩
  intros x h_feas_x
  rw [h_objFun _ h_feas_y, phi_left_inv]
  have h_bound := h_opt_y.2 (Rx.phi x) (Rx.phi_feasibility x h_feas_x)
  rwa [← h_objFun _ h_feas_x] at h_bound

def ofStrongEquivalence (E : p ≡' q) : p ≽' q :=
  { phi := E.phi,
    phi_feasibility := E.phi_feasibility,
    phi_optimality := E.phi_optimality }

instance : Trans (@Relaxation D E R _) (@StrongEquivalence E F R _) (@Relaxation D F R _) :=
  { trans := fun R E => Relaxation.trans R (ofStrongEquivalence E) }

instance : Trans (@StrongEquivalence D E R _) (@Relaxation E F R _) (@Relaxation D F R _) :=
  { trans := fun E R => Relaxation.trans (ofStrongEquivalence E) R }

end Relaxation

namespace StrongEquivalence

variable {p q}

@[strong_equiv]
def ofRelaxations (Rx₁ : p ≽' q) (Rx₂ : q ≽' p) : p ≡' q :=
  { phi := Rx₁.phi,
    psi := Rx₂.phi,
    phi_feasibility := Rx₁.phi_feasibility,
    psi_feasibility := Rx₂.phi_feasibility,
    phi_optimality := Rx₁.phi_optimality,
    psi_optimality := Rx₂.phi_optimality }

end StrongEquivalence

namespace Equivalence

variable {p q}

@[equiv]
def ofRelaxations (Rx₁ : p ≽' q) (Rx₂ : q ≽' p) : p ≡ q :=
  Equivalence.ofStrongEquivalence (StrongEquivalence.ofRelaxations Rx₁ Rx₂)

end Equivalence

namespace Relaxation

variable {f : D → R} {cs : D → Prop}

@[rel]
def remove_constraint {c cs' : D → Prop} (hcs : ∀ x, cs x ↔ c x ∧ cs' x) : ⟨f, cs⟩ ≽' ⟨f, cs'⟩ :=
  { phi := id,
    phi_feasibility := fun x h_feas_x => ((hcs x).mp h_feas_x).2,
    phi_optimality := fun _ _ => le_refl _ }

@[rel]
def weaken_constraints (cs' : D → Prop) (hcs : ∀ x, cs x → cs' x) : ⟨f, cs⟩ ≽' ⟨f, cs'⟩ :=
  { phi := id,
    phi_feasibility := fun x h_feas_x => hcs x h_feas_x,
    phi_optimality := fun _ _ => le_refl _ }

end Relaxation

end Minimization
