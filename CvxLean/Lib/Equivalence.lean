import CvxLean.Lib.Math.Data.Real
import CvxLean.Lib.Minimization

/-!
# Equivalence of optimization problems

TODO
-/

variable {R D E F : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)
/-
  p := min { f(x) | c_p(x) }
  q := min { g(x) | c_q(x) }
  r := min { h(x) | c_r(x) }
-/

namespace Minimization

/-- Regular notion of equivalence between optimization problems. -/
structure Equivalence where
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.feasible x → q.feasible (phi x)
  psi_feasibility : ∀ y, q.feasible y → p.feasible (psi y)
  phi_optimality : ∀ x, p.optimal x → q.optimal (phi x)
  psi_optimality : ∀ x, q.optimal x → p.optimal (psi x)

namespace Equivalence

def refl : Equivalence p p :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hy => hy,
    phi_optimality := fun _ hx => hx,
    psi_optimality := fun _ hx => hx }

def symm (E : Equivalence p q) : Equivalence q p :=
  { phi := E.psi,
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    psi_feasibility := E.phi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

def trans (E₁ : Equivalence p q) (E₂ : Equivalence q r) : Equivalence p r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx => E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    psi_feasibility := fun y hy => E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    phi_optimality := fun x hx => E₂.phi_optimality (E₁.phi x) (E₁.phi_optimality x hx),
    psi_optimality := fun y hy => E₁.psi_optimality (E₂.psi y) (E₂.psi_optimality y hy) }

instance : Trans (@Equivalence R D E _) (@Equivalence R E F _) (@Equivalence R D F _) :=
  { trans := fun E₁ E₂ => Equivalence.trans _ _ _ E₁ E₂ }

variable {p q}

def toFwd (E : Equivalence p q) : Solution p → Solution q :=
  fun sol => {
    point := E.phi sol.point,
    feasibility := E.phi_feasibility sol.point sol.feasibility,
    optimality := E.phi_optimality sol.point ⟨sol.feasibility, sol.optimality⟩ |>.right }

def toBwd (E : Equivalence p q) : Solution q → Solution p :=
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

def refl : StrongEquivalence p p :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hy => hy,
    phi_optimality := fun _ _ => le_refl _,
    psi_optimality := fun _ _ => le_refl _ }

def symm (E : StrongEquivalence p q) : StrongEquivalence q p :=
  { phi := E.psi,
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    psi_feasibility := E.phi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_optimality := E.phi_optimality }

def trans (E₁ : StrongEquivalence p q) (E₂ : StrongEquivalence q r) :
  StrongEquivalence p r :=
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx => E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    psi_feasibility := fun y hy => E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    phi_optimality := fun x hx =>
      -- h(φ₂(φ₁(x))) ≤ g(φ₁(x))
      have h₁ := E₂.phi_optimality (E₁.phi x) (E₁.phi_feasibility x hx)
      -- g(φ₁(x)) <= f(x)
      have h₂ := E₁.phi_optimality x hx
      le_trans h₁ h₂,
    psi_optimality := fun y hy =>
      -- f(ψ₁(ψ₂(y))) <= g(ψ₂(y))
      have h₁ := E₁.psi_optimality (E₂.psi y) (E₂.psi_feasibility y hy)
      -- g(ψ₂(y)) <= h(y)
      have h₂ := E₂.psi_optimality y hy
      le_trans h₁ h₂
  }

instance :
  Trans (@StrongEquivalence R D E _) (@StrongEquivalence R E F _) (@StrongEquivalence R D F _) :=
  { trans := fun E₁ E₂ => StrongEquivalence.trans _ _ _ E₁ E₂ }

variable {p q}

/-- As expected, an equivalence can be built from a strong equivalence. -/
def toEquivalence (E : StrongEquivalence p q) : Equivalence p q :=
  { phi := E.phi,
    psi := E.psi,
    phi_feasibility := E.phi_feasibility,
    psi_feasibility := E.psi_feasibility,
    phi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨E.phi_feasibility x h_feas_x,
       fun y h_feas_y =>
        -- g(φ(x)) <= f(x)
        have h₁ := E.phi_optimality x h_feas_x
        -- f(x) <= f(ψ(y))
        have h₂ := h_opt_x (E.psi y) (E.psi_feasibility y h_feas_y)
        -- f(ψ(y)) <= g(y)
        have h₃ := E.psi_optimality y h_feas_y
        le_trans (le_trans h₁ h₂) h₃⟩,
    psi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨E.psi_feasibility x h_feas_x,
       fun y h_feas_y =>
        have h₁ := E.psi_optimality x h_feas_x
        -- f(ψ(x)) <= g(x)
        have h₂ := h_opt_x (E.phi y) (E.phi_feasibility y h_feas_y)
        -- g(x) <= g(φ(y))
        have h₃ := E.phi_optimality y h_feas_y
        -- g(φ(y)) <= f(y)
        le_trans (le_trans h₁ h₂) h₃⟩ }

def toFwd (E : StrongEquivalence p q) : Solution p → Solution q :=
  E.toEquivalence.toFwd

def StrongEquivalence.toBwd (E : StrongEquivalence p q) : Solution q → Solution p :=
  E.toEquivalence.toBwd

end StrongEquivalence

namespace Equivalence

noncomputable section Maps

def map_objFun_log {cs : D → Prop} {f : D → ℝ} (h : ∀ x, cs x → f x > 0) :
    Equivalence ⟨f, cs⟩ ⟨fun x => (Real.log (f x)), cs⟩ :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hx => hx,
    phi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x,
       fun y h_feas_y =>
        have h_fx_le_fy := h_opt_x y h_feas_y
        have h_fx_pos := h x h_feas_x
        have h_fy_pos := h y h_feas_y
        (Real.log_le_log h_fx_pos h_fy_pos).mpr h_fx_le_fy⟩
    psi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x,
       fun y h_feas_y =>
        have h_logfx_le_logfy := h_opt_x y h_feas_y
        have h_fx_pos := h x h_feas_x
        have h_fy_pos := h y h_feas_y
        (Real.log_le_log h_fx_pos h_fy_pos).mp h_logfx_le_logfy⟩ }

def map_objFun_sq {cs : D → Prop} {f : D → ℝ} (h : ∀ x, cs x → f x ≥ 0) :
    Equivalence ⟨f, cs⟩ ⟨fun x => (f x) ^ (2 : ℝ), cs⟩ :=
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx,
    psi_feasibility := fun _ hx => hx,
    phi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x,
       fun y h_feas_y => by
        have h_fx_le_fy := h_opt_x y h_feas_y
        have h_fx_pos := h x h_feas_x
        have h_fy_pos := h y h_feas_y
        simpa [sq_le_sq, abs_of_nonneg h_fx_pos, abs_of_nonneg h_fy_pos]⟩,
    psi_optimality := fun x ⟨h_feas_x, h_opt_x⟩ =>
      ⟨h_feas_x,
       fun y h_feas_y => by
        have h_sqfx_le_sqfy := h_opt_x y h_feas_y
        have h_fx_pos := h x h_feas_x
        have h_fy_pos := h y h_feas_y
        simp [sq_le_sq, abs_of_nonneg h_fx_pos, abs_of_nonneg h_fy_pos] at h_sqfx_le_sqfy
        exact h_sqfx_le_sqfy⟩ }

def map_domain {f : D → R} {cs : D → Prop} {fwd : D → E} {bwd : E → D}
    (h : ∀ x, cs x → bwd (fwd x) = x) :
    Equivalence ⟨f, cs⟩ ⟨fun x => f (bwd x), (fun x => cs (bwd x))⟩ :=
  StrongEquivalence.toEquivalence <|
  { phi := fwd,
    psi := bwd,
    phi_feasibility := fun {x} hx => by simp [h x hx]; exact hx
    phi_optimality := fun {x} hx => by simp [h x hx]
    psi_feasibility := fun _ hx => hx
    psi_optimality := fun {x} _ => by simp }

end Maps

section Rewrites

def rewrite_objective {D R} [Preorder R] {f g : D → R} {cs : D → Prop}
  (hrw : ∀ x, cs x → f x = g x) :
  Equivalence
    (Minimization.mk f cs)
    (Minimization.mk g cs) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun _ hx => hx
    phi_optimality := fun {x} hx => le_of_eq (hrw x hx).symm
    psi_feasibility := fun _ hx => hx
    psi_optimality := fun {x} hx => le_of_eq (hrw x hx) }

def rewrite_constraint_1 {D R} [Preorder R] {c1 c1' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, cs x → (c1 x ↔ c1' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1  x ∧ cs x))
    (Minimization.mk f (fun x => c1' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_1_last {D R} [Preorder R] {c1 c1' : D → Prop} {f : D → R}
  (hrw : ∀ x, (c1 x ↔ c1' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1  x))
    (Minimization.mk f (fun x => c1' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_2 {D R} [Preorder R] {c1 c2 c2' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → cs x → (c2 x ↔ c2' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_2_last {D R} [Preorder R] {c1 c2 c2' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → (c2 x ↔ c2' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2  x))
    (Minimization.mk f (fun x => c1 x ∧ c2' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_3 {D R} [Preorder R] {c1 c2 c3 c3' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → cs x → (c3 x ↔ c3' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_3_last {D R} [Preorder R] {c1 c2 c3 c3' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → (c3 x ↔ c3' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_4 {D R} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → cs x → (c4 x ↔ c4' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_4_last {D R} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → (c4 x ↔ c4' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_5 {D R} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → cs x → (c5 x ↔ c5' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_5_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → (c5 x ↔ c5' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_6 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → cs x → (c6 x ↔ c6' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_6_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → (c6 x ↔ c6' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_7 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → cs x → (c7 x ↔ c7' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_7_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → (c7 x ↔ c7' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_8 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → cs x → (c8 x ↔ c8' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_8_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → (c8 x ↔ c8' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_9 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → cs x → (c9 x ↔ c9' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_9_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → (c9 x ↔ c9' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_10 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → cs x → (c10 x ↔ c10' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10  x ∧ cs x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x ∧ cs x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_10_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → (c10 x ↔ c10' x)) :
  Equivalence
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10  x))
    (Minimization.mk f (fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x)) :=
  StrongEquivalence.toEquivalence <|
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

end Rewrites

end Equivalence

end Minimization
