import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Minimization
import CvxLean.Meta.Attributes

/-!
# Equivalence of optimization problems

We define equivalence and strong equivalence, and several equivalence-preserving transformations.

## References

* [S. Boyd and L. Vandenberghe, *Convex Optimization*][BV04]
* [M. C. Grant, *Discipliend Convex Programming*][Gra05]
-/

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)

/- Let `p := ⟨f, cs⟩`, `q := ⟨g, ds⟩` and `r := ⟨h, es⟩`. -/

/-- Regular notion of equivalence between optimization problems. We require maps `(φ, ψ)` between
teh domains of `p` and `q` such that they map optimal points to optimal points. -/
structure Equivalence where
  phi : D → E
  psi : E → D
  phi_optimality : ∀ x, p.optimal x → q.optimal (phi x)
  psi_optimality : ∀ x, q.optimal x → p.optimal (psi x)

namespace Equivalence

variable {p q r}

notation p " ≡ " q => Equivalence p q

@[equiv]
def refl : p ≡ p :=
  { phi := id,
    psi := id,
    phi_optimality := fun _ hx => hx,
    psi_optimality := fun _ hx => hx }

@[equiv]
def symm (E : p ≡ q) : q ≡ p :=
  { phi := E.psi,
    psi := E.phi,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

@[equiv]
def trans (E₁ : p ≡ q) (E₂ : q ≡ r) : p ≡ r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_optimality := fun x hx => E₂.phi_optimality (E₁.phi x) (E₁.phi_optimality x hx),
    psi_optimality := fun y hy => E₁.psi_optimality (E₂.psi y) (E₂.psi_optimality y hy) }

instance : Trans (@Equivalence D E R _) (@Equivalence E F R _) (@Equivalence D F R _) :=
  { trans := Equivalence.trans }

/-- An equivalence induces a map between the solution set of `p` and the solution set of `q`. -/
def toFwd (E : p ≡ q) : Solution p → Solution q :=
  fun sol =>
    { point := E.phi sol.point,
      isOptimal := E.phi_optimality sol.point sol.isOptimal }

/-- An equivalence induces a map between the solution set of `q` and the solution set of `p`. -/
def toBwd (E : p ≡ q) : Solution q → Solution p :=
  fun sol =>
    { point := E.psi sol.point,
      isOptimal := E.psi_optimality sol.point sol.isOptimal }

end Equivalence

/-- Notion of equivalence used by the DCP procedure. It makes some proofs simpler. The
optimality-preserving requirements of `(φ, ψ)` are replaced by:
* for every `p`-feasible `x`, `g(φ(x)) ≤ f(x)`, i.e. `φ` gives a lower bound of `f`.
* for every `q`-feasible `y`, `f(ψ(y)) ≤ g(y)`, i.e. `ψ` fives a lower bound of `g`.  -/
structure StrongEquivalence where
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.feasible x → q.feasible (phi x)
  psi_feasibility : ∀ y, q.feasible y → p.feasible (psi y)
  phi_optimality : ∀ x, p.feasible x → q.objFun (phi x) ≤ p.objFun x
  psi_optimality : ∀ y, q.feasible y → p.objFun (psi y) ≤ q.objFun y

namespace StrongEquivalence

variable {p q r}

notation p " ≡' " q => StrongEquivalence p q

@[strong_equiv]
def refl : p ≡' p :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hy => hy,
    phi_optimality := fun _ _ => le_refl _,
    psi_optimality := fun _ _ => le_refl _ }

@[strong_equiv]
def symm (E : p ≡' q) : q ≡' p :=
  { phi := E.psi,
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    psi_feasibility := E.phi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

@[strong_equiv]
def trans (E₁ : p ≡' q) (E₂ : q ≡' r) : p ≡' r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx => E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    psi_feasibility := fun y hy => E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    phi_optimality := fun x hx =>
      -- `h(φ₂(φ₁(x))) ≤ g(φ₁(x))`
      have h₁ := E₂.phi_optimality (E₁.phi x) (E₁.phi_feasibility x hx)
      -- `g(φ₁(x)) ≤ f(x)`
      have h₂ := E₁.phi_optimality x hx
      le_trans h₁ h₂,
    psi_optimality := fun y hy =>
      -- `f(ψ₁(ψ₂(y))) ≤ g(ψ₂(y))`
      have h₁ := E₁.psi_optimality (E₂.psi y) (E₂.psi_feasibility y hy)
      -- `g(ψ₂(y)) ≤ h(y)`
      have h₂ := E₂.psi_optimality y hy
      le_trans h₁ h₂ }

instance :
    Trans (@StrongEquivalence D E R _) (@StrongEquivalence E F R _) (@StrongEquivalence D F R _) :=
  { trans := StrongEquivalence.trans }

end StrongEquivalence

namespace Equivalence

section Eq

variable {p q : Minimization D R}

/-- Equal problems are equivalent. Note that the domain needs to be the same. We intentionally do
not define this as `h ▸ Equivalence.refl (p := p)` so that `phi` and `psi` can be easily
extracted. -/
@[equiv]
def ofEq (h : p = q) : p ≡ q :=
  { phi := id,
    psi := id,
    phi_optimality := fun _ hx => h ▸ hx,
    psi_optimality := fun _ hy => h ▸ hy }

end Eq

variable {p q}


/-- As expected, an `Equivalence` can be built from a `StrongEquivalence`. -/
@[equiv]
def ofStrongEquivalence (E : p ≡' q) : p ≡ q :=
  { phi := E.phi,
    psi := E.psi,
    phi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨E.phi_feasibility x h_feas_x,
       fun y h_feas_y =>
        -- `g(φ(x)) ≤ f(x)`
        have h₁ := E.phi_optimality x h_feas_x
        -- `f(x) ≤ f(ψ(y))`
        have h₂ := h_opt_x (E.psi y) (E.psi_feasibility y h_feas_y)
        -- `f(ψ(y)) ≤ g(y)`
        have h₃ := E.psi_optimality y h_feas_y
        le_trans (le_trans h₁ h₂) h₃⟩,
    psi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨E.psi_feasibility x h_feas_x,
       fun y h_feas_y =>
        have h₁ := E.psi_optimality x h_feas_x
        -- `f(ψ(x)) ≤ g(x)`
        have h₂ := h_opt_x (E.phi y) (E.phi_feasibility y h_feas_y)
        -- `g(x) ≤ g(φ(y))`
        have h₃ := E.phi_optimality y h_feas_y
        -- `g(φ(y)) ≤ f(y)`
        le_trans (le_trans h₁ h₂) h₃⟩ }

instance : Trans (@StrongEquivalence D E R _) (@Equivalence E F R _) (@Equivalence D F R _) :=
  { trans := fun S E => Equivalence.trans (ofStrongEquivalence S) E }

instance : Trans (@Equivalence D E R _) (@StrongEquivalence E F R _) (@Equivalence D F R _) :=
  { trans := fun E S => Equivalence.trans E (ofStrongEquivalence S) }

end Equivalence

namespace StrongEquivalence

open Equivalence

def toFwd (E : p ≡' q) : Solution p → Solution q :=
  (ofStrongEquivalence E).toFwd

def toBwd (E : p ≡' q) : Solution q → Solution p :=
  (ofStrongEquivalence E).toBwd

end StrongEquivalence

namespace Equivalence

/- Mapping the objective function by monotonic functions yields an equivalence. Also, mapping the
whole domain by a function with a right inverse. -/
section Maps

/-- See [BV04,p.131] where `g` is `ψ₀`. -/
@[equiv]
def map_objFun {g : R → R} (h : ∀ {r s}, cs r → cs s → (g (f r) ≤ g (f s) ↔ f r ≤ f s)) :
    ⟨f, cs⟩ ≡ ⟨fun x => g (f x), cs⟩ :=
  { phi := id,
    psi := id,
    phi_optimality := fun _ ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x, fun y h_feas_y => (h h_feas_x h_feas_y).mpr (h_opt_x y h_feas_y)⟩,
    psi_optimality := fun _ ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x, fun y h_feas_y => (h h_feas_x h_feas_y).mp (h_opt_x y h_feas_y)⟩ }

@[equiv]
noncomputable def map_objFun_log {f : D → ℝ} (h : ∀ x, cs x → f x > 0) :
    ⟨f, cs⟩ ≡ ⟨fun x => (Real.log (f x)), cs⟩ := by
  apply map_objFun
  intros r s h_feas_r h_feas_s
  exact Real.log_le_log_iff (h r h_feas_r) (h s h_feas_s)

@[equiv]
noncomputable def map_objFun_sq {f : D → ℝ} (h : ∀ x, cs x → f x ≥ 0) :
    ⟨f, cs⟩ ≡ ⟨fun x => (f x) ^ (2 : ℝ), cs⟩ := by
  apply map_objFun (g := fun x => x ^ (2 : ℝ))
  intros r s h_feas_r h_feas_s
  simp [sq_le_sq, abs_of_nonneg (h r h_feas_r), abs_of_nonneg (h s h_feas_s)]

/-- This is simply a change of variables, see `ChangeOfVariables.toEquivalence` and [BV04,p.130]. -/
@[equiv]
def map_domain {f : D → R} {cs : D → Prop} {fwd : D → E} {bwd : E → D}
    (h : ∀ x, cs x → bwd (fwd x) = x) :
    ⟨f, cs⟩ ≡ ⟨fun x => f (bwd x), fun x => cs (bwd x)⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fwd,
    psi := bwd,
    phi_feasibility := fun {x} hx => by simp [feasible, h x hx]; exact hx,
    psi_feasibility := fun _ hx => hx,
    phi_optimality := fun {x} hx => by simp [h x hx],
    psi_optimality := fun {x} _ => by simp }

end Maps

/- Rewriting the objective function or the constraints leads to equivalent problems. -/
section Rewrites

variable {f : D → R}
variable {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : D → Prop}
variable {c1' c2' c3' c4' c5' c6' c7' c8' c9' c10' : D → Prop}
variable {cs cs' : D → Prop}
variable {g : D → R}

/-- We assume constraints are joind by `∧`. A problem with several constraints can be written as
`⟨f, [[c1, ..., cn]]⟩`. -/
syntax (name := constrNotation) "[ [" term,* "] ]" : term

macro_rules
  | `([[]]) => `(fun x => True)
  | `([[$c]]) => `(fun x => $c x)
  | `([[$c1, $c2]]) => `(fun x => $c1 x ∧ $c2 x)
  | `([[$c1, $c2, $c3]]) => `(fun x => $c1 x ∧ $c2 x ∧ $c3 x)
  | `([[$c1, $c2, $c3, $c4]]) => `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x)
  | `([[$c1, $c2, $c3, $c4, $c5]]) => `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x ∧ $c5 x)
  | `([[$c1, $c2, $c3, $c4, $c5, $c6]]) => `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x ∧ $c5 x ∧ $c6 x)
  | `([[$c1, $c2, $c3, $c4, $c5, $c6, $c7]]) =>
      `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x ∧ $c5 x ∧ $c6 x ∧ $c7 x)
  | `([[$c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8]]) =>
      `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x ∧ $c5 x ∧ $c6 x ∧ $c7 x ∧ $c8 x)
  | `([[$c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8, $c9]]) =>
      `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x ∧ $c5 x ∧ $c6 x ∧ $c7 x ∧ $c8 x ∧ $c9 x)
  | `([[$c1, $c2, $c3, $c4, $c5, $c6, $c7, $c8, $c9, $c10]]) =>
      `(fun x => $c1 x ∧ $c2 x ∧ $c3 x ∧ $c4 x ∧ $c5 x ∧ $c6 x ∧ $c7 x ∧ $c8 x ∧ $c9 x ∧ $c10 x)
  | `([[$c, $cs,*]]) => `(fun x => $c x ∧ ([[$cs,*]] x))

@[equiv]
def rewrite_objFun (hrw : ∀ x, cs x → f x = g x) : ⟨f, cs⟩ ≡ ⟨g, cs⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx
    psi_feasibility := fun _ hx => hx
    phi_optimality := fun {x} hx => le_of_eq (hrw x hx).symm
    psi_optimality := fun {x} hx => le_of_eq (hrw x hx) }

@[equiv]
def rewrite_objFun_1 (hrw : ∀ x, c1 x → f x = g x) : ⟨f, c1⟩ ≡ ⟨g, c1⟩ :=
  rewrite_objFun hrw

@[equiv]
def rewrite_objFun_2 (hrw : ∀ x, c1 x → c2 x → f x = g x) : ⟨f, [[c1, c2]]⟩ ≡ ⟨g, [[c1, c2]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_3 (hrw : ∀ x, c1 x → c2 x → c3 x → f x = g x) :
    ⟨f, [[c1, c2, c3]]⟩ ≡ ⟨g, [[c1, c2, c3]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_4 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4]]⟩ ≡ ⟨g, [[c1, c2, c3, c4]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_5 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4, c5]]⟩ ≡ ⟨g, [[c1, c2, c3, c4, c5]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_6 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4, c5, c6]]⟩ ≡ ⟨g, [[c1, c2, c3, c4, c5, c6]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_7 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7]]⟩ ≡ ⟨g, [[c1, c2, c3, c4, c5, c6, c7]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_8 (hrw :
    ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8]]⟩ ≡ ⟨g, [[c1, c2, c3, c4, c5, c6, c7, c8]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_9
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9]]⟩ ≡
    ⟨g, [[c1, c2, c3, c4, c5, c6, c7, c8, c9]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

@[equiv]
def rewrite_objFun_10
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → c10 x → f x = g x) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]]⟩ ≡
    ⟨g, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]]⟩ :=
  rewrite_objFun (fun x _ => by apply hrw x <;> tauto)

/- Helper tactics to build equivalences from rewriting constraints in one line. -/
section EquivalenceOfConstrRw

open Lean.Parser.Tactic

macro "prove_phi_feasibility_of_rw_constr" hrw:ident : tactic =>
  `(tactic| (simp [feasible]; intros; rw [← $hrw] <;> tauto))

macro "prove_psi_feasibility_of_rw_constr" hrw:ident : tactic =>
  `(tactic| (simp [feasible]; intros; rw [($hrw)] <;> tauto))

macro "equivalence_of_rw_constr" hrw:ident : term =>
  `(Equivalence.ofStrongEquivalence <|
    { phi := id,
      psi := id,
      phi_feasibility := by prove_phi_feasibility_of_rw_constr $hrw
      psi_feasibility := by prove_psi_feasibility_of_rw_constr $hrw
      phi_optimality := fun {x} _ => le_refl _
      psi_optimality := fun {x} _ => le_refl _ })

end EquivalenceOfConstrRw

@[equiv]
def rewrite_constraints (hrw : ∀ x, cs x ↔ cs' x) : ⟨f, [[cs]]⟩ ≡ ⟨f, [[cs']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_1 (hrw : ∀ x, cs x → (c1 x ↔ c1' x)) : ⟨f, [[c1, cs]]⟩ ≡ ⟨f, [[c1', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_1_last (hrw : ∀ x, c1 x ↔ c1' x) : ⟨f, [[c1]]⟩ ≡ ⟨f, [[c1']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_2 (hrw : ∀ x, c1 x → cs x → (c2 x ↔ c2' x)) :
    ⟨f, [[c1, c2, cs]]⟩ ≡ ⟨f, [[c1, c2', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_2_last (hrw : ∀ x, c1 x → (c2 x ↔ c2' x)) :
    ⟨f, [[c1, c2]]⟩ ≡ ⟨f, [[c1, c2']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_3 (hrw : ∀ x, c1 x → c2 x → cs x → (c3 x ↔ c3' x)) :
    ⟨f, [[c1, c2, c3, cs]]⟩ ≡ ⟨f, [[c1, c2, c3', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_3_last (hrw : ∀ x, c1 x → c2 x → (c3 x ↔ c3' x)) :
    ⟨f, [[c1, c2, c3]]⟩ ≡ ⟨f, [[c1, c2, c3']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_4 (hrw : ∀ x, c1 x → c2 x → c3 x → cs x → (c4 x ↔ c4' x)) :
    ⟨f, [[c1, c2, c3, c4, cs]]⟩ ≡ ⟨f, [[c1, c2, c3, c4', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_4_last (hrw : ∀ x, c1 x → c2 x → c3 x → (c4 x ↔ c4' x)) :
    ⟨f, [[c1, c2, c3, c4]]⟩ ≡ ⟨f, [[c1, c2, c3, c4']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_5 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → cs x → (c5 x ↔ c5' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, cs]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_5_last (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → (c5 x ↔ c5' x)) :
    ⟨f, [[c1, c2, c3, c4, c5]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_6 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → cs x → (c6 x ↔ c6' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, cs]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5, c6', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_6_last (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → (c6 x ↔ c6' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5, c6']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_7
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → cs x → (c7 x ↔ c7' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, cs]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5, c6, c7', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_7_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → (c7 x ↔ c7' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5, c6, c7']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_8
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → cs x → (c8 x ↔ c8' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, cs]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_8_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → (c8 x ↔ c8' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8]]⟩ ≡ ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_9
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → cs x → (c9 x ↔ c9' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, cs]]⟩ ≡
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_9_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → (c9 x ↔ c9' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9]]⟩ ≡
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9']]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_10
    (hrw :
      ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → cs x → (c10 x ↔ c10' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, cs]]⟩ ≡
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10', cs]]⟩ :=
  equivalence_of_rw_constr hrw

@[equiv]
def rewrite_constraint_10_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → (c10 x ↔ c10' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]]⟩ ≡
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10']]⟩ :=
  equivalence_of_rw_constr hrw

end Rewrites

/- Other equivalence-preserving transformations. These are not used by any tactic but can be used
directly. They provide evidence that our notion of equivalence captures the expected
transformations. -/
section Other

variable {f : D → R} {cs : D → Prop}

/-- We can always add a redundant constraint. This might be useful to help the reduction algorithm
infer some constraints that cannot be easily infered by `arith`. -/
@[equiv]
def add_constraint {cs' : D → Prop} (h : ∀ x, cs x → cs' x) : ⟨f, cs⟩ ≡ ⟨f, [[cs', cs]]⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hcs => ⟨h _ hcs, hcs⟩,
    psi_feasibility := fun _ ⟨_, hcs⟩ => hcs,
    phi_optimality := fun _ _ => le_refl _,
    psi_optimality := fun _ _ => le_refl _ }

/-- See [BV04,p.131] where `g` is `ψᵢ`. -/
@[equiv]
def map_le_constraint_standard_form [Zero R] {cs' : D → Prop} {fi : D → R} {g : R → R}
    (hcs : ∀ x, cs x ↔ fi x ≤ 0 ∧ cs' x) (hg : ∀ x, g x ≤ 0 ↔ x ≤ 0) :
    ⟨f, cs⟩ ≡ ⟨f, fun x => g (fi x) ≤ 0 ∧ cs' x⟩ := by
  apply rewrite_constraints; intros x; rw [hcs x, hg (fi x)]

/-- See [BV04,p.131] where `g` is `ψₘ₊ᵢ`. -/
@[equiv]
def map_eq_constraint_standard_form [Zero R] {cs' : D → Prop} {hi : D → R} {g : R → R}
    (hcs : ∀ x, cs x ↔ hi x = 0 ∧ cs' x) (hg : ∀ x, g x = 0 ↔ x = 0) :
    ⟨f, cs⟩ ≡ ⟨f, fun x => g (hi x) = 0 ∧ cs' x⟩ := by
  apply rewrite_constraints; intros x; rw [hcs x, hg (hi x)]

/-- Adding a slack variable [BV04,p.131]. -/
@[equiv]
def add_slack_variable_standard_form {cs' : D → Prop} {fi : D → ℝ}
    (hcs : ∀ x, cs x ↔ fi x ≤ 0 ∧ cs' x) :
    ⟨f, cs⟩ ≡ ⟨fun (_, x) => f x, fun (si, x) => 0 ≤ (si : ℝ) ∧ fi x + si = 0 ∧ cs' x⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (-fi x, x),
    psi := fun (_, x) => x,
    phi_feasibility := fun {x} h_feas_x => by
      simp [feasible, hcs x] at h_feas_x ⊢; exact h_feas_x,
    psi_feasibility := fun (si, x) ⟨hsi, hfi, hc⟩ => by
      simp [feasible, hcs x]; refine ⟨?_, hc⟩; linarith
    phi_optimality := fun {x} _ => le_refl _,
    psi_optimality := fun (_, x) _ => by simp }

/-- Eliminate equality constraints [BV04,p.132]. -/
@[equiv]
noncomputable def eliminate_eq_constraint_standard_form [Inhabited E] {cs' : D → Prop} {hi : D → ℝ}
    {g : E → D} (hcs : ∀ x, cs x ↔ hi x = 0 ∧ cs' x) (hg : ∀ x, hi x = 0 ↔ ∃ z, x = g z) :
    ⟨f, cs⟩ ≡ ⟨fun x => f (g x), fun x => cs' (g x)⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => if h : hi x = 0 then Classical.choose ((hg x).mp h) else default,
    psi := g,
    phi_feasibility := fun {x} h_feas_x => by
      simp [feasible, hcs x] at h_feas_x ⊢
      replace ⟨h_hix_eq_0, h_cx⟩ := h_feas_x
      simp [h_hix_eq_0]
      rwa [Classical.choose_spec ((hg x).mp h_hix_eq_0)] at h_cx
    psi_feasibility := fun x h_feas_x => by
      simp [feasible, hcs (g x)]
      refine ⟨?_, h_feas_x⟩
      rw [hg (g x)]
      exact ⟨x, rfl⟩
    phi_optimality := fun {x} h_feas_x => by
      simp [feasible, hcs x] at h_feas_x ⊢
      replace ⟨h_hix_eq_0, _⟩ := h_feas_x
      simp [h_hix_eq_0]
      rw [congr_arg f <| Classical.choose_spec ((hg x).mp h_hix_eq_0)],
    psi_optimality := fun x _ => by simp }

/-- Decompose constraint by introducing another equality constraint [BV04,p.132]. -/
@[equiv]
def decompose_constraint (g : D → E) (cs' : D → E → Prop) (hc : ∀ x, cs x ↔ cs' x (g x)) :
    ⟨f, cs⟩ ≡ ⟨fun (x, _) => f x, fun (x, y) => y = g x ∧ cs' x y⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (x, g x),
    psi := fun (x, _) => x,
    phi_feasibility := fun {x} h_feas_x => by simpa [feasible, ← hc, h_feas_x],
    psi_feasibility := fun (x, y) ⟨h_x_eq_gy, h_cyx⟩ => by simp [feasible, hc, h_x_eq_gy ▸ h_cyx],
    phi_optimality := fun {_} _ => le_refl _,
    psi_optimality := fun {_} _ => le_refl _ }

/-- Epigraph form [BV04,p.134]. -/
@[equiv]
def epigraph_form : ⟨f, cs⟩ ≡ ⟨fun (t, _) => t, fun (t, x) => f x ≤ t ∧ cs x⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (f x, x),
    psi := fun (_, x) => x,
    phi_feasibility := fun {x} h_feas_x => by simpa [feasible],
    psi_feasibility := fun (t, x) ⟨_, h_csx⟩ => by simpa [feasible],
    phi_optimality := fun {_} _ => le_refl _,
    psi_optimality := fun {_} ⟨h_fx_le_t, _⟩ => by simpa }

/-- Suppose `D ≃ S × E`. Let problem `p := ⟨f, cs⟩` be defined over `D`. Every `x : D` maps
one-to-one to `(s, y) : S × E`. Assume that `x` is `p`-feasible iff `s = g y` and `cs' x`. We can
think of `s` as a new variable. If changing `s` does not change the objective function and the new
constraints `c` respect monotonicity in `S`, we have that `p` is equivalent to the problem
`⟨f, s ≤ g y ∧ cs' x⟩`. -/
@[equiv]
def eq_to_le_left {S} [Preorder S] (e : D ≃ S × E) (g : E → S) (cs' : D → Prop)
    (hcs : ∀ {x}, cs x ↔ ((e x).1 = g (e x).2 ∧ cs' x))
    (hf : ∀ y r s, f (e.symm (r, y)) = f (e.symm (s, y)))
    (h_mono: ∀ y r s, r ≤ s → cs' (e.symm (r, y)) → cs' (e.symm (s, y))) :
    ⟨f, cs⟩ ≡ ⟨f, fun x => (e x).1 ≤ g (e x).2 ∧ cs' x⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => x,
    psi := fun x => e.symm (g (e x).2, (e x).2),
    phi_feasibility := fun {x} h_feas_x => ⟨le_of_eq (hcs.1 h_feas_x).1, (hcs.1 h_feas_x).2⟩,
    psi_feasibility := fun {x} h_feas_x => by
      have hcx : cs' x := h_feas_x.2
      have hcegex : cs' (e.symm (g (e x).2, (e x).2)) := by
        apply h_mono (e x).2 (e x).1 _ h_feas_x.1; simp [hcx]
      simp [feasible, hcs, hcegex]
    phi_optimality := fun {x} _ => le_refl _,
    psi_optimality := fun {x} _ => by simp; rw [hf _ _ (e x).1]; simp [le_of_eq] }

/-- Similar to `eq_to_le_left` with the monotonicity condition on `c` flipped. In this case we have
that `P` is equivalent to `⟨f, g y ≤ s ∧ cs' x⟩`. -/
@[equiv]
def eq_to_le_right {S} [Preorder S] (e : Equiv D (S × E)) (g : E → S) (cs' : D → Prop)
    (hcs : ∀ {x}, cs x ↔ (g (e x).2 = (e x).1 ∧ cs' x))
    (hf : ∀ x r s, f (e.symm ⟨r, x⟩) = f (e.symm ⟨s, x⟩))
    (h_mono : ∀ x r s, r ≤ s → cs' (e.symm (s, x)) → cs' (e.symm ⟨r, x⟩)) :
    ⟨f, cs⟩ ≡  ⟨f, fun x => g (e x).2 ≤ (e x).1 ∧ cs' x⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => x,
    psi := fun x => e.symm ⟨g (e x).2, (e x).2⟩,
    phi_feasibility := fun {x} h_feas_x => ⟨le_of_eq (hcs.1 h_feas_x).1, (hcs.1 h_feas_x).2⟩,
    psi_feasibility := fun {x} h_feas_x => by
      have hcx : cs' x := h_feas_x.2
      have hcegex : cs' (e.symm ⟨g (e x).2, (e x).2⟩) := by
        apply h_mono (e x).2 _ (e x).1 h_feas_x.1; simp [hcx]
      simp [feasible, hcs, hcegex]
    phi_optimality := fun {x} _ => le_refl _,
    psi_optimality := fun {x} _ => by simp; rw [hf _ _ (e x).1]; simp [le_of_eq] }

/-- Changing the domain to an equivalent type yields an equivalent problem. -/
@[equiv]
def domain_equiv (e : E ≃ D) : ⟨f, cs⟩ ≡ ⟨f ∘ e, cs ∘ e⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := e.symm,
    psi := e,
    phi_feasibility := fun {x} h_feas_x => by simpa [feasible],
    psi_feasibility := fun {x} h_feas_x => by simpa [feasible],
    phi_optimality := fun {x} _ => by simp,
    psi_optimality := fun {x} _ => by simp }

/-- Introduce a new variable `s` that replaces occurrences of (non-linear) `g x` in the original
problem. The resulting problem has an extra constraint `s ≤ g y`. The objective funciton and the
rest of the constraints need to satisfy the appropriate monotonicity conditions [Gra05,4.2.1]. -/
@[equiv]
def linearization_mono {S} [Preorder S] (g : D → S) (c : S → D → Prop) (h : S → D → R)
    (hf : ∀ x, f x = h (g x) x)
    (hcs : ∀ x, cs x = c (g x) x)
    (h_mono_f : ∀ x r s, r ≤ s → h s x ≤ h r x)
    (h_mono_cs : ∀ x r s, r ≤ s → c r x → c s x) :
    ⟨f, cs⟩ ≡ ⟨fun (s, y) => h s y, fun (s, y) => s ≤ g y ∧ c s y⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (g x, x),
    psi := fun (_, y) => y,
    phi_feasibility := fun {x} h_feas_x => ⟨le_refl _, hcs x ▸ h_feas_x⟩,
    psi_feasibility := fun (s, y) ⟨h_s_le_gy, h_csy⟩ => by
      simp only [feasible, hcs]; exact h_mono_cs y _ _ h_s_le_gy h_csy
    phi_optimality := fun {x} _ => le_of_eq (hf _).symm,
    psi_optimality := fun (s, y) h_feas_sy => by
      simp only [hf]; exact h_mono_f y _ _ h_feas_sy.1 }

/-- Similar to `linearization_mono` with the monotonicity conditions flipped. The resulting problem
adds the exactra constraint `g y ≤ s` in this case [Gra05,4.2.1]. -/
@[equiv]
def linearization_antimono {S} [Preorder S] (g : D → S) (c : S → D → Prop) (h : S → D → R)
    (hf : ∀ x, f x = h (g x) x)
    (hcs : ∀ x, cs x = c (g x) x)
    (h_mono_f : ∀ x r s, r ≤ s → h r x ≤ h s x)
    (h_mono_cs : ∀ x r s, r ≤ s → c s x → c r x) :
    ⟨f, cs⟩ ≡ ⟨fun (s, y) => h s y, fun (s, y) => g y ≤ s ∧ c s y⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (g x, x),
    psi := fun (_, y) => y,
    phi_feasibility := fun {x} h_feas_x => ⟨le_refl _, hcs x ▸ h_feas_x⟩,
    psi_feasibility := fun (s, y) ⟨h_gy_le_s, h_csy⟩ => by
      simp only [feasible, hcs]; exact h_mono_cs y _ _ h_gy_le_s h_csy
    phi_optimality := fun {x} _ => le_of_eq (hf _).symm,
    psi_optimality := fun (s, y) h_feas_sy => by
      simp only [hf]; exact h_mono_f y _ _ h_feas_sy.1 }

/-- This can be seen as a generalization of `linearization_mono`, where `d` is the graph
implementation of `g`. This is not used by the DCP procedure. -/
@[equiv]
def graph_expansion_greatest {S} [Preorder S] (g : D → S) (c d : S → D → Prop) (h : S → D → R)
    (hg : ∀ x v, c v x → IsGreatest {y | d y x} (g x))
    (hf : ∀ x, f x = h (g x) x)
    (hcs : ∀ x, cs x = c (g x) x)
    (h_mono_f : ∀ x r s, r ≤ s → h s x ≤ h r x)
    (h_mono_cs : ∀ x r s, r ≤ s → c r x → c s x) :
    ⟨f, cs⟩ ≡ ⟨fun (s, y) => h s y, fun (s, y) => d s y ∧ c s y⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (g x, x),
    psi := fun (_, y) => y,
    phi_feasibility := fun {x} h_feas_x => by
      simp only [feasible, hcs] at h_feas_x; exact ⟨(hg x (g x) h_feas_x).1, h_feas_x⟩,
    psi_feasibility := fun (s, y) ⟨h_dsy, h_csy⟩ => by
      simp only [feasible, hcs]; exact h_mono_cs y _ _ ((hg y s h_csy).2 h_dsy) h_csy
    phi_optimality := fun {x} _ => le_of_eq (hf _).symm,
    psi_optimality := fun (s, y) h_feas_sy => by
      simp only [hf]; exact h_mono_f y _ _ ((hg y s h_feas_sy.2).2 h_feas_sy.1) }

/-- Similar to `graph_expansion_greatest` but in the flipped monotonicity context, c.f.
`linearization_antimono`. This is not used by the DCP procedure. -/
@[equiv]
def graph_expansion_least {S} [Preorder S] (g : D → S) (c d : S → D → Prop) (h : S → D → R)
    (hg : ∀ x v, c v x → IsLeast {y | d y x} (g x))
    (hf : ∀ x, f x = h (g x) x)
    (hcs : ∀ x, cs x = c (g x) x)
    (h_mono_f : ∀ x r s, r ≤ s → h r x ≤ h s x)
    (h_mono_cs : ∀ x r s, r ≤ s → c s x → c r x) :
    ⟨f, cs⟩ ≡ ⟨fun (s, y) => h s y, fun (s, y) => d s y ∧ c s y⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (g x, x),
    psi := fun (_, y) => y,
    phi_feasibility := fun {x} h_feas_x => by
      simp only [feasible, hcs] at h_feas_x; exact ⟨(hg x (g x) h_feas_x).1, h_feas_x⟩,
    psi_feasibility := fun (s, y) ⟨h_dsy, h_csy⟩ => by
      simp only [feasible, hcs]; exact h_mono_cs y _ _ ((hg y s h_csy).2 h_dsy) h_csy
    phi_optimality := fun {x} _ => le_of_eq (hf _).symm,
    psi_optimality := fun (s, y) h_feas_sy => by
      simp only [hf]; exact h_mono_f y _ _ ((hg y s h_feas_sy.2).2 h_feas_sy.1) }

/-- Version of `graph_expansion_least` that works with vectors. -/
@[equiv]
def graph_expansion_least_forall {S I : Type} [Preorder S] [Inhabited I] (g : D → I → S)
    (c d : S → D → Prop) (hg : ∀ x v i, c v x → IsLeast {y | d y x} (g x i))
    (hcs : ∀ x, cs x = ∀ i, c (g x i) x) (h_mono_cs : ∀ x r s, r ≤ s → c s x → c r x) :
    ⟨f, cs⟩ ≡
    ⟨fun sy : (I → S) × D => f sy.2,
     fun sy : (I → S) × D => (∀ i, d (sy.1 i) sy.2) ∧ (∀ i, c (sy.1 i) sy.2)⟩ :=
  graph_expansion_least (f := f) (cs := cs) (g := g) (c := fun y x => ∀ i, c (y i) x)
    (d := fun y x => ∀ i, d (y i) x) (h := fun _ x => f x)
    (hg := fun x v hc =>
      ⟨fun i => (hg x (v i) i (hc i)).1, fun _ c i => (hg x (v i) i (hc i)).2 (c i)⟩)
    (hf := fun _ => rfl) (hcs := hcs) (h_mono_f := fun _ _ _ _ => le_refl _)
    (h_mono_cs := fun x r s hrs hc i => h_mono_cs x (r i) (s i) (hrs i) (hc i))

end Other

end Equivalence

end Minimization
