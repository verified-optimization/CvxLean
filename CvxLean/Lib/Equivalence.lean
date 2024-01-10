import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Minimization

/-!
# Equivalence of optimization problems

We define equivalence and strong equivalence, and several equivalence-preserving transformations.
-/

namespace Minimization

variable {D E F R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)
/-
  p := min { f(x) | c_p(x) }
  q := min { g(x) | c_q(x) }
  r := min { h(x) | c_r(x) }
-/

/-- Regular notion of equivalence between optimization problems. -/
structure Equivalence where
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.feasible x → q.feasible (phi x)
  psi_feasibility : ∀ y, q.feasible y → p.feasible (psi y)
  phi_optimality : ∀ x, p.optimal x → q.optimal (phi x)
  psi_optimality : ∀ x, q.optimal x → p.optimal (psi x)

namespace Equivalence

variable {p q r}

notation p " ≃ " q => Equivalence p q

def refl : p ≃ p :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hy => hy,
    phi_optimality := fun _ hx => hx,
    psi_optimality := fun _ hx => hx }

def symm (E : p ≃ q) : q ≃ p :=
  { phi := E.psi,
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    psi_feasibility := E.phi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

def trans (E₁ : p ≃ q) (E₂ : q ≃ r) : p ≃ r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx => E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    psi_feasibility := fun y hy => E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    phi_optimality := fun x hx => E₂.phi_optimality (E₁.phi x) (E₁.phi_optimality x hx),
    psi_optimality := fun y hy => E₁.psi_optimality (E₂.psi y) (E₂.psi_optimality y hy) }

instance : Trans (@Equivalence D E R _) (@Equivalence E F R _) (@Equivalence D F R _) :=
  { trans := Equivalence.trans }

def toFwd (E : p ≃ q) : Solution p → Solution q :=
  fun sol => {
    point := E.phi sol.point,
    feasibility := E.phi_feasibility sol.point sol.feasibility,
    optimality := E.phi_optimality sol.point ⟨sol.feasibility, sol.optimality⟩ |>.right }

def toBwd (E : p ≃ q) : Solution q → Solution p :=
  fun sol => {
    point := E.psi sol.point,
    feasibility := E.psi_feasibility sol.point sol.feasibility,
    optimality := E.psi_optimality sol.point ⟨sol.feasibility, sol.optimality⟩ |>.right }

end Equivalence

/-- Notion of equivalence used by the DCP procedure. -/
structure StrongEquivalence where
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.constraints x → q.constraints (phi x)
  psi_feasibility : ∀ y, q.constraints y → p.constraints (psi y)
  phi_optimality : ∀ x, p.constraints x → q.objFun (phi x) ≤ p.objFun x
  psi_optimality : ∀ y, q.constraints y → p.objFun (psi y) ≤ q.objFun y

namespace StrongEquivalence

variable {p q r}

notation p " ≃ₛ " q => StrongEquivalence p q

def refl : p ≃ₛ p :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hy => hy,
    phi_optimality := fun _ _ => le_refl _,
    psi_optimality := fun _ _ => le_refl _ }

def symm (E : p ≃ₛ q) : q ≃ₛ p :=
  { phi := E.psi,
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    psi_feasibility := E.phi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

def trans (E₁ : p ≃ₛ q) (E₂ : q ≃ₛ r) : p ≃ₛ r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx => E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    psi_feasibility := fun y hy => E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    phi_optimality := fun x hx =>
      -- h(φ₂(φ₁(x))) ≤ g(φ₁(x))
      have h₁ := E₂.phi_optimality (E₁.phi x) (E₁.phi_feasibility x hx)
      -- g(φ₁(x)) ≤ f(x)
      have h₂ := E₁.phi_optimality x hx
      le_trans h₁ h₂,
    psi_optimality := fun y hy =>
      -- f(ψ₁(ψ₂(y))) ≤ g(ψ₂(y))
      have h₁ := E₁.psi_optimality (E₂.psi y) (E₂.psi_feasibility y hy)
      -- g(ψ₂(y)) ≤ h(y)
      have h₂ := E₂.psi_optimality y hy
      le_trans h₁ h₂
  }

instance :
    Trans (@StrongEquivalence D E R _) (@StrongEquivalence E F R _) (@StrongEquivalence D F R _) :=
  { trans := StrongEquivalence.trans }

end StrongEquivalence

namespace Equivalence

variable {p q}

/-- As expected, an equivalence can be built from a strong equivalence. -/
def ofStrongEquivalence (E : p ≃ₛ q) : p ≃ q :=
  { phi := E.phi,
    psi := E.psi,
    phi_feasibility := E.phi_feasibility,
    psi_feasibility := E.psi_feasibility,
    phi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨E.phi_feasibility x h_feas_x,
       fun y h_feas_y =>
        -- g(φ(x)) ≤ f(x)
        have h₁ := E.phi_optimality x h_feas_x
        -- f(x) ≤ f(ψ(y))
        have h₂ := h_opt_x (E.psi y) (E.psi_feasibility y h_feas_y)
        -- f(ψ(y)) ≤ g(y)
        have h₃ := E.psi_optimality y h_feas_y
        le_trans (le_trans h₁ h₂) h₃⟩,
    psi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨E.psi_feasibility x h_feas_x,
       fun y h_feas_y =>
        have h₁ := E.psi_optimality x h_feas_x
        -- f(ψ(x)) ≤ g(x)
        have h₂ := h_opt_x (E.phi y) (E.phi_feasibility y h_feas_y)
        -- g(x) ≤ g(φ(y))
        have h₃ := E.phi_optimality y h_feas_y
        -- g(φ(y)) ≤ f(y)
        le_trans (le_trans h₁ h₂) h₃⟩ }

instance : Trans (@StrongEquivalence D E R _) (@Equivalence E F R _) (@Equivalence D F R _) :=
  { trans := fun S E => Equivalence.trans (ofStrongEquivalence S) E }

instance : Trans (@Equivalence D E R _) (@StrongEquivalence E F R _) (@Equivalence D F R _) :=
  { trans := fun E S => Equivalence.trans E (ofStrongEquivalence S) }

end Equivalence

namespace StrongEquivalence

open Equivalence

def toFwd (E : p ≃ₛ q) : Solution p → Solution q :=
  (ofStrongEquivalence E).toFwd

def toBwd (E : p ≃ₛ q) : Solution q → Solution p :=
  (ofStrongEquivalence E).toBwd

end StrongEquivalence

namespace Equivalence

/- Mapping the objective function by monotonic functions yields an equivalence. Also, mapping the
whole domain by a function with a right inverse. -/
section Maps

def map_objFun {g : R → R}
    (h : ∀ {r s}, cs r → cs s → (g (f r) ≤ g (f s) ↔ f r ≤ f s)) :
    ⟨f, cs⟩ ≃ ⟨fun x => g (f x), cs⟩ :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hx => hx,
    phi_optimality := fun _ ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x, fun y h_feas_y => (h h_feas_x h_feas_y).mpr (h_opt_x y h_feas_y)⟩,
    psi_optimality := fun _ ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x, fun y h_feas_y => (h h_feas_x h_feas_y).mp (h_opt_x y h_feas_y)⟩ }

noncomputable def map_objFun_log {f : D → ℝ} (h : ∀ x, cs x → f x > 0) :
    ⟨f, cs⟩ ≃ ⟨fun x => (Real.log (f x)), cs⟩ := by
  apply map_objFun
  intros r s h_feas_r h_feas_s
  exact Real.log_le_log (h r h_feas_r) (h s h_feas_s)

noncomputable def map_objFun_sq {f : D → ℝ} (h : ∀ x, cs x → f x ≥ 0) :
    ⟨f, cs⟩ ≃ ⟨fun x => (f x) ^ (2 : ℝ), cs⟩ := by
  apply map_objFun (g := fun x => x ^ (2 : ℝ))
  intros r s h_feas_r h_feas_s
  simp [sq_le_sq, abs_of_nonneg (h r h_feas_r), abs_of_nonneg (h s h_feas_s)]

def map_domain {f : D → R} {cs : D → Prop} {fwd : D → E} {bwd : E → D}
    (h : ∀ x, cs x → bwd (fwd x) = x) :
    ⟨f, cs⟩ ≃ ⟨fun x => f (bwd x), (fun x => cs (bwd x))⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fwd,
    psi := bwd,
    phi_feasibility := fun {x} hx => by simp [h x hx]; exact hx,
    psi_feasibility := fun _ hx => hx,
    phi_optimality := fun {x} hx => by simp [h x hx],
    psi_optimality := fun {x} _ => by simp }

end Maps

/- Rewriting the objective function or the constraints leads to equivalent problems. -/
section Rewrites

variable {f g : D → R}
variable {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : D → Prop}
variable {c1' c2' c3' c4' c5' c6' c7' c8' c9' c10' : D → Prop}
variable {cs cs' : D → Prop}

def rewrite_objFun (hrw : ∀ x, cs x → f x = g x) : ⟨f, cs⟩ ≃ ⟨g, cs⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx
    psi_feasibility := fun _ hx => hx
    phi_optimality := fun {x} hx => le_of_eq (hrw x hx).symm
    psi_optimality := fun {x} hx => le_of_eq (hrw x hx) }

/- Helper tactics to build equivalences from rewriting constraints in one line. -/
section EquivalenceOfConstrRw

open Lean.Parser.Tactic

macro "prove_phi_feasibility_of_rw_constr" hrw:ident : tactic =>
  `(tactic| (simp [constraints]; intros; rw [← $hrw] <;> tauto))

macro "prove_psi_feasibility_of_rw_constr" hrw:ident : tactic =>
  `(tactic| (simp [constraints]; intros; rw [($hrw)] <;> tauto))

macro "equivalence_of_rw_constr" hrw:ident : term =>
  `(Equivalence.ofStrongEquivalence <|
    { phi := id,
      psi := id,
      phi_feasibility := by prove_phi_feasibility_of_rw_constr $hrw
      psi_feasibility := by prove_psi_feasibility_of_rw_constr $hrw
      phi_optimality := fun {x} _ => le_refl _
      psi_optimality := fun {x} _ => le_refl _ })

end EquivalenceOfConstrRw

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

def rewrite_constraints (hrw : ∀ x, cs x ↔ cs' x) : ⟨f, [[cs]]⟩ ≃ ⟨f, [[cs']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_1 (hrw : ∀ x, cs x → (c1 x ↔ c1' x)) : ⟨f, [[c1, cs]]⟩ ≃ ⟨f, [[c1', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_1_last (hrw : ∀ x, c1 x ↔ c1' x) : ⟨f, [[c1]]⟩ ≃ ⟨f, [[c1']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_2 (hrw : ∀ x, c1 x → cs x → (c2 x ↔ c2' x)) :
    ⟨f, [[c1, c2, cs]]⟩ ≃ ⟨f, [[c1, c2', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_2_last (hrw : ∀ x, c1 x → (c2 x ↔ c2' x)) :
    ⟨f, [[c1, c2]]⟩ ≃ ⟨f, [[c1, c2']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_3 (hrw : ∀ x, c1 x → c2 x → cs x → (c3 x ↔ c3' x)) :
    ⟨f, [[c1, c2, c3, cs]]⟩ ≃ ⟨f, [[c1, c2, c3', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_3_last (hrw : ∀ x, c1 x → c2 x → (c3 x ↔ c3' x)) :
    ⟨f, [[c1, c2, c3]]⟩ ≃ ⟨f, [[c1, c2, c3']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_4 (hrw : ∀ x, c1 x → c2 x → c3 x → cs x → (c4 x ↔ c4' x)) :
    ⟨f, [[c1, c2, c3, c4, cs]]⟩ ≃ ⟨f, [[c1, c2, c3, c4', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_4_last (hrw : ∀ x, c1 x → c2 x → c3 x → (c4 x ↔ c4' x)) :
    ⟨f, [[c1, c2, c3, c4]]⟩ ≃ ⟨f, [[c1, c2, c3, c4']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_5 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → cs x → (c5 x ↔ c5' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, cs]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_5_last (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → (c5 x ↔ c5' x)) :
    ⟨f, [[c1, c2, c3, c4, c5]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_6 (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → cs x → (c6 x ↔ c6' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, cs]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5, c6', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_6_last (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → (c6 x ↔ c6' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5, c6']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_7
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → cs x → (c7 x ↔ c7' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, cs]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5, c6, c7', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_7_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → (c7 x ↔ c7' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5, c6, c7']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_8
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → cs x → (c8 x ↔ c8' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, cs]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_8_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → (c8 x ↔ c8' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8]]⟩ ≃ ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_9
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → cs x → (c9 x ↔ c9' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, cs]]⟩ ≃
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_9_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → (c9 x ↔ c9' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9]]⟩ ≃
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9']]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_10
    (hrw :
      ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → cs x → (c10 x ↔ c10' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, cs]]⟩ ≃
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10', cs]]⟩ :=
  equivalence_of_rw_constr hrw

def rewrite_constraint_10_last
    (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → (c10 x ↔ c10' x)) :
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]]⟩ ≃
    ⟨f, [[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10']]⟩ :=
  equivalence_of_rw_constr hrw

end Rewrites

/- Other equivalence-preserving transformations. -/
section Other

variable {cs : D → Prop} {f : D → R}

/-- Decompose constraint by adding another equality constraint. -/
def decompose_constraint (g : D → E) (c : D → E → Prop) (hc : ∀ x, cs x = c x (g x)) :
    ⟨f, cs⟩ ≃ ⟨fun (_, y) => f y, fun (x, y) => x = g y ∧ c y x⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => (g x, x),
    psi := fun (_, y) => y,
    phi_feasibility := fun {x} h_feas_x => by simpa [feasible, ← hc, h_feas_x],
    psi_feasibility := fun (x, y) ⟨h_x_eq_gy, h_cyx⟩ => by simp [feasible, hc, h_x_eq_gy ▸ h_cyx],
    phi_optimality := fun {_} _ => le_refl _,
    psi_optimality := fun {_} _ => le_refl _ }

-- TODO

-- def eq_to_le_left
--   (e: Equiv D (S × E)) (f : E → S) (c : D → Prop)
--   (hc : ∀ {x}, p.constraints x ↔ ((e.toFun x).1 = f (e.toFun x).2 ∧ c x))
--   (h_objFun : ∀ x r s, p.objFun (e.symm.toFun (r,x)) = p.objFun (e.symm.toFun (s,x)))
--   (h_mono: ∀ x r s, r ≤ s → c (e.symm.toFun (r, x)) → c (e.symm.toFun (s, x)))
--   (sol : Solution
--     { objFun := p.objFun,
--       constraints := fun x => (e.toFun x).1 ≤ f (e.toFun x).2 ∧ c x } ) :
--   p.Solution :=
-- simple_reduction p _ sol
--   (fun x => x) (fun x => e.symm.toFun ⟨f (e.toFun x).2, (e.toFun x).2⟩)
--   (fun {x} hx => le_refl _)
--   (fun {x} hx => by
--     rw [h_objFun _ _ ((e.toFun x).1)]
--     simp [le_of_eq])
--   (fun {x} hx => ⟨le_of_eq (hc.1 hx).1, (hc.1 hx).2⟩)
--   (fun {x} hx => by
--     have : c (e.symm.toFun (f (e.toFun x).2, (e.toFun x).2)) := by
--       apply h_mono
--       apply hx.1
--       simp [hx.2]
--     simp_all )

-- /-- -/
-- def eq_to_le_right
--   (e: Equiv D (S × E)) (f : E → S) (c : D → Prop)
--   (hc : ∀ {x}, p.constraints x ↔ (f (e.toFun x).2 = (e.toFun x).1 ∧ c x))
--   (h_objFun : ∀ x r s, p.objFun (e.symm.toFun ⟨r, x⟩) = p.objFun (e.symm.toFun ⟨s, x⟩))
--   (h_mono: ∀ x r s, r ≤ s → c (e.symm.toFun (s, x)) → c (e.symm.toFun ⟨r, x⟩))
--   (sol : Solution
--     { objFun := p.objFun,
--       constraints := fun x => f (e.toFun x).2 ≤ (e.toFun x).1 ∧ c x }) :
--   p.Solution :=
-- simple_reduction p _ sol
--   (fun x => x) (fun x => e.symm.toFun ⟨f (e.toFun x).2, (e.toFun x).2⟩)
--   (fun {x} hx => le_refl _)
--   (fun {x} hx => by
--     rw [h_objFun _ _ ((e.toFun x).1)]
--     simp [le_of_eq])
--   (fun {x} hx => ⟨le_of_eq (hc.1 hx).1, (hc.1 hx).2⟩)
--   (fun {x} hx => by
--     have : c (e.symm.toFun (f (e.toFun x).2, (e.toFun x).2)) := by
--       apply h_mono
--       apply hx.1
--       simp [hx.2]
--     simp_all)

-- /-- -/
-- def linearization_mono {of : D → R} {cs : D → Prop}
--   {S : Type}
--   {g : D → S} {c : S → D → Prop} {f : S → D → R}
--   {hS : Preorder S}
--   (hof : ∀ x, of x = f (g x) x)
--   (hcs : ∀ x, cs x = c (g x) x)
--   (h_mono_of: ∀ x r s, r ≤ s → f s x ≤ f r x)
--   (h_mono_cs: ∀ x r s, r ≤ s → c r x → c s x)
--   (sol : Solution
--       { objFun := fun (y : S × D) => f y.1 y.2,
--         constraints := fun y => y.1 ≤ g y.2 ∧ c y.1 y.2 }) :
--   Solution {objFun := of, constraints := cs} :=
-- simple_reduction _ _ sol
--   (fun x => (g x, x)) (fun x => x.2)
--   (fun {x} hx => le_of_eq (hof _).symm)
--   (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ hx.1)
--   (fun {x} hx => by simp only [hcs] at hx; exact ⟨le_refl _, hx⟩)
--   (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ hx.1 hx.2)

-- /-- -/
-- def linearization_antimono {of : D → R} {cs : D → Prop}
--   {S : Type}
--   {g : D → S} {c : S → D → Prop} {f : S → D → R}
--   {hS : Preorder S}
--   (hof : ∀ x, of x = f (g x) x)
--   (hcs : ∀ x, cs x = c (g x) x)
--   (h_mono_of: ∀ x r s, r ≤ s → f r x ≤ f s x)
--   (h_mono_cs: ∀ x r s, r ≤ s → c s x → c r x)
--   (sol : Solution
--       { objFun := fun (y : S × D) => f y.1 y.2,
--         constraints := fun y => g y.2 ≤ y.1 ∧ c y.1 y.2 }) :
--   Solution {objFun := of, constraints := cs} :=
-- simple_reduction _ _ sol
--   (fun x => (g x, x)) (fun x => x.2)
--   (fun {x} hx => le_of_eq (hof _).symm)
--   (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ hx.1)
--   (fun {x} hx => by simp only [hcs] at hx; exact ⟨le_refl _, hx⟩)
--   (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ hx.1 hx.2)

-- /-- -/
-- def graph_expansion_greatest {of : D → R} {cs : D → Prop}
--   {S : Type}
--   {g : D → S} {c d : S → D → Prop} {f : S → D → R}
--   {hS : Preorder S}
--   (hg : ∀ x v, c v x → IsGreatest {y | d y x} (g x))
--   (hof : ∀ x, of x = f (g x) x)
--   (hcs : ∀ x, cs x = c (g x) x)
--   (h_mono_of: ∀ x r s, r ≤ s → f s x ≤ f r x)
--   (h_mono_cs: ∀ x r s, r ≤ s → c r x → c s x)
--   (sol : Solution
--       { objFun := fun (y : S × D) => f y.1 y.2,
--         constraints := fun (y : S × D) => d y.1 y.2 ∧ c y.1 y.2 })  :
--   Solution {objFun := of, constraints := cs} :=
-- simple_reduction _ _ sol
--   (fun x => (g x, x)) (fun x => x.2)
--   (fun hx => le_of_eq (hof _).symm)
--   (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1))
--   (fun {x} hx => by simp only [hcs] at hx; exact ⟨(hg x (g x) hx).1, hx⟩)
--   (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1) hx.2)

-- /-- -/
-- def graph_expansion_least {of : D → R} {cs : D → Prop}
--   {S : Type}
--   {g : D → S} {c d : S → D → Prop} {f : S → D → R}
--   {hS : Preorder S}
--   (hg : ∀ x v, c v x → IsLeast {y | d y x} (g x))
--   (hof : ∀ x, of x = f (g x) x)
--   (hcs : ∀ x, cs x = c (g x) x)
--   (h_mono_of: ∀ x r s, r ≤ s → f r x ≤ f s x)
--   (h_mono_cs: ∀ x r s, r ≤ s → c s x → c r x)
--   (sol : Solution
--       { objFun := fun (y : S × D) => f y.1 y.2,
--         constraints := fun (y : S × D) => d y.1 y.2 ∧ c y.1 y.2 })  :
--   Solution {objFun := of, constraints := cs} :=
-- simple_reduction _ _ sol
--   (fun x => (g x, x)) (fun x => x.2)
--   (fun hx => le_of_eq (hof _).symm)
--   (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1))
--   (fun {x} hx => by simp only [hcs] at hx; exact ⟨(hg x (g x) hx).1, hx⟩)
--   (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1) hx.2)

-- /-- TODO: This is probably better done in a tactic? -/
-- def graph_expansion_least_forall {of : D → R} {cs : D → Prop}
--   {I S : Type} [Inhabited I]
--   {g : D → I → S} {h : D → I → S} {c d : S → D → Prop}
--   {hS : Preorder S}
--   (hg : ∀ x v i, c v x → IsLeast {y | d y x} (g x i))
--   (hcs : ∀ x, cs x = ∀ i, c (g x i) x)
--   (h_mono_cs: ∀ x r s, r ≤ s → c s x → c r x)
--   (sol : Solution
--       { objFun := fun (y : (I → S) × D) => of y.2,
--         constraints := fun (y : (I → S) × D) => (∀ i, d (y.1 i) y.2) ∧ (∀ i, c (y.1 i) y.2) })  :
--   Solution {objFun := of, constraints := cs} :=
--   @graph_expansion_least D R _ of cs (I → S) g
--     (fun y x => ∀ i, c (y i) x)
--     (fun y x => ∀ i, d (y i) x)
--     (fun y x => of x)
--     ⟨fun a i => le_refl (a i),
--      fun a b c hab hbc i => le_trans (hab i) (hbc i),
--      fun a b => Iff.refl _⟩
--     (fun x v hc => ⟨fun i => (hg x (v i) i (hc i)).1,
--      fun v' c i => (hg x (v i) i (hc i)).2 (c i)⟩)
--     (fun x => rfl)
--     hcs
--     (fun x r s hrs => le_refl _)
--     (fun x r s hrs hc i => h_mono_cs x (r i) (s i) (hrs i) (hc i))
--     sol

-- /-- Change domain to equivalent type. -/
-- noncomputable def domain_equiv {D E : Type} (e : Equiv E D)
--   (R : Type) [Preorder R]
--   (f : D → R) (cs : D → Prop)
--   (sol : Solution
--     { objFun := f ∘ e.toFun,
--       constraints := cs ∘ e.toFun}) :
-- Solution
--   { objFun := f,
--     constraints := cs } :=
-- simple_reduction _ _ sol e.symm.toFun e.toFun
--   (fun _ => by simp [Function.comp])
--   (fun _ => by simp)
--   (fun {x} hx => by simp [Function.comp]; exact hx)
--   (fun {x} hx => by simp; exact hx)

end Other

end Equivalence

end Minimization
