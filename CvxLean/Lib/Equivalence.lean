import CvxLean.Lib.Minimization 
import CvxLean.Lib.Missing.Real
import CvxLean.Syntax.Minimization


variable {R D E F : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)
/-
  p := min { f(x) | c_p(x) }
  q := min { g(x) | c_q(x) }
  r := min { h(x) | c_r(x) }
-/

namespace Minimization

structure StrongEquivalence where 
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.constraints x → q.constraints (phi x)
  phi_optimality : ∀ x, p.constraints x → q.objFun (phi x) ≤ p.objFun x
  psi_feasibility : ∀ y, q.constraints y → p.constraints (psi y)
  psi_optimality : ∀ y, q.constraints y → p.objFun (psi y) ≤ q.objFun y

def StrongEquivalence.toFwd (E : StrongEquivalence p q) : Solution p → Solution q := 
  fun sol => {
    point := E.phi sol.point, 
    feasibility := E.phi_feasibility sol.point sol.feasibility, 
    optimality := fun y => by
      -- g(phi(x)) <= f(x)
      have h₁ := E.phi_optimality sol.point sol.feasibility;
      -- f(x) <= f(psi(y))
      let psi_y : p.FeasPoint := 
        ⟨E.psi y.point, E.psi_feasibility y.point y.feasibility⟩
      have h₂ := sol.optimality psi_y;
      -- f(psi(y)) <= g(y)
      have h₃ := E.psi_optimality y.point y.feasibility;
      exact le_trans (le_trans h₁ h₂) h₃
  }

def StrongEquivalence.toBwd (E : StrongEquivalence p q) : Solution q → Solution p := 
  fun sol => {
    point := E.psi sol.point,
    feasibility := E.psi_feasibility sol.point sol.feasibility,
    optimality := fun y => by
      -- f(psi(x)) <= g(x)
      have h₁ := E.psi_optimality sol.point sol.feasibility;
      -- g(x) <= g(phi(y))
      let phi_y : q.FeasPoint := 
        ⟨E.phi y.point, E.phi_feasibility y.point y.feasibility⟩
      have h₂ := sol.optimality phi_y;
      -- g(phi(y)) <= f(y)
      have h₃ := E.phi_optimality y.point y.feasibility;
      exact le_trans (le_trans h₁ h₂) h₃
  }

def StrongEquivalence.refl : StrongEquivalence p p := 
  { phi := id, 
    psi := id,
    phi_feasibility := fun _ hx => hx,
    phi_optimality := fun _ _ => le_refl _,
    psi_feasibility := fun _ hy => hy,
    psi_optimality := fun _ _ => le_refl _ }

def StrongEquivalence.symm (E : StrongEquivalence p q) : StrongEquivalence q p := 
  { phi := E.psi, 
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_feasibility := E.phi_feasibility,
    psi_optimality := E.phi_optimality }

def StrongEquivalence.trans (E₁ : StrongEquivalence p q) (E₂ : StrongEquivalence q r) : 
  StrongEquivalence p r := 
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx =>
      E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    phi_optimality := fun x hx => by
      -- h(phi₂(phi₁(x))) <= g(phi₁(x))
      have h₁ := E₂.phi_optimality (E₁.phi x) (E₁.phi_feasibility x hx);
      -- g(phi₁(x)) <= f(x)
      have h₂ := E₁.phi_optimality x hx;
      exact le_trans h₁ h₂,
    psi_feasibility := fun y hy =>
      E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    psi_optimality := fun y hy => by 
      -- f(psi₁(psi₂(y))) <= g(psi₂(y))
      have h₁ := E₁.psi_optimality (E₂.psi y) (E₂.psi_feasibility y hy);
      -- g(psi₂(y)) <= h(y)
      have h₂ := E₂.psi_optimality y hy;
      exact le_trans h₁ h₂
  }

instance : 
  Trans (@StrongEquivalence R D E _) (@StrongEquivalence R E F _) (@StrongEquivalence R D F _) := 
  { trans := fun E₁ E₂ => StrongEquivalence.trans _ _ _ E₁ E₂ }

end Minimization

open Minimization

-- NOTE(RFM): B for bundled. 

structure MinimizationB (R) [Preorder R] := 
  (D : Type)
  (prob : Minimization D R)

def MinimizationB.equiv : MinimizationB R → MinimizationB R → Prop := 
  fun p q => Nonempty (StrongEquivalence p.prob q.prob)

lemma MinimizationB.equiv_refl (p : MinimizationB R) : 
  MinimizationB.equiv p p :=
  ⟨StrongEquivalence.refl _⟩

lemma MinimizationB.equiv_symm {p q : MinimizationB R} : 
  MinimizationB.equiv p q → MinimizationB.equiv q p :=
  fun ⟨E⟩ => ⟨@StrongEquivalence.symm R p.D q.D _ p.prob q.prob E⟩ 

lemma MinimizationB.equiv_trans {p q r : MinimizationB R} : 
  MinimizationB.equiv p q → MinimizationB.equiv q r → MinimizationB.equiv p r :=
  fun ⟨E₁⟩ ⟨E₂⟩ => 
    ⟨@StrongEquivalence.trans R p.D q.D r.D _ p.prob q.prob r.prob E₁ E₂⟩   

instance : Setoid (MinimizationB R) := 
  { r := MinimizationB.equiv,
    iseqv := 
      { refl := MinimizationB.equiv_refl, 
        symm := MinimizationB.equiv_symm, 
        trans := MinimizationB.equiv_trans } }

-- NOTE(RFM): Q for quotient.

def MinimizationQ := @Quotient (MinimizationB R) (by infer_instance)

def MinimizationQ.mk {D : Type} (p : Minimization D R) : @MinimizationQ R _ := 
  Quotient.mk' { D := D, prob := p }

syntax "{|" term "|}" : term

macro_rules
  | `({| $p:term |}) => `(@MinimizationQ.mk _ _ _ $p)

syntax "{|" term ", " term "|}" : term

macro_rules 
  | `({| $f:term , $cs:term |}) => 
    `({| { objFun := $f, constraints := $cs } |})

namespace Delab

open Lean Lean.PrettyPrinter.Delaborator SubExpr Meta 
open CvxLean CvxLean.Delab
 
@[delab app]
def delabMinimizationQ : Delab := do
  match ← getExpr with
  | .app (.app (.app (.app (.const `MinimizationQ.mk _) _) _) _) p => 
    let pStx ← withExpr p delab
    `({| $pStx |})
  | _ => Alternative.failure

end Delab


/- Rewrites used in `convexify` under the `equivalence` command. -/
namespace MinimizationQ

section Rewrites

def rewrite_objective {D R} [Preorder R] {f g : D → R} {cs : D → Prop} 
  (hrw : ∀ x, cs x → f x = g x) :
  {| f, cs |} = {| g, cs |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun _ hx => hx
    phi_optimality := fun {x} hx => le_of_eq (hrw x hx).symm
    psi_feasibility := fun _ hx => hx
    psi_optimality := fun {x} hx => le_of_eq (hrw x hx) }

def rewrite_constraint_1 {D R} [Preorder R] {c1 c1' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, cs x → (c1 x ↔ c1' x)) :
  {| f, fun x => c1  x ∧ cs x |} = 
  {| f, fun x => c1' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_1_last {D R} [Preorder R] {c1 c1' : D → Prop} {f : D → R}
  (hrw : ∀ x, (c1 x ↔ c1' x)) :
  {| f, fun x => c1  x |} =
  {| f, fun x => c1' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_2 {D R} [Preorder R] {c1 c2 c2' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → cs x → (c2 x ↔ c2' x)) :
  {| f, fun x => c1 x ∧ c2  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_2_last {D R} [Preorder R] {c1 c2 c2' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → (c2 x ↔ c2' x)) :
  {| f, fun x => c1 x ∧ c2  x |} = 
  {| f, fun x => c1 x ∧ c2' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_3 {D R} [Preorder R] {c1 c2 c3 c3' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → cs x → (c3 x ↔ c3' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_3_last {D R} [Preorder R] {c1 c2 c3 c3' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → (c3 x ↔ c3' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_4 {D R} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → cs x → (c4 x ↔ c4' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_4_last {D R} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → (c4 x ↔ c4' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_5 {D R} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → cs x → (c5 x ↔ c5' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_5_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → (c5 x ↔ c5' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_6 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → cs x → (c6 x ↔ c6' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_6_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → (c6 x ↔ c6' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_7 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → cs x → (c7 x ↔ c7' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_7_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → (c7 x ↔ c7' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_8 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → cs x → (c8 x ↔ c8' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_8_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → (c8 x ↔ c8' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_9 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → cs x → (c9 x ↔ c9' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_9_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → (c9 x ↔ c9' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_10 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → cs x → (c10 x ↔ c10' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10  x ∧ cs x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x ∧ cs x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

def rewrite_constraint_10_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → (c10 x ↔ c10' x)) :
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10  x |} = 
  {| f, fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun x hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1] at hx; exact hx
    phi_optimality := fun {x} _ => le_refl _
    psi_feasibility := fun x hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1] at hx; exact hx
    psi_optimality := fun {x} _ => le_refl _ }

end Rewrites

end MinimizationQ

-- NOTE(RFM): Experiment with Props.

def Solution' : Prop := 
  ∃ point : D, 
      p.constraints point 
    ∧ ∀ y : p.FeasPoint, p.objFun point ≤ p.objFun y.point

def Φ : Solution p → Solution' p := 
  fun ⟨x, hxf, hxo⟩ => ⟨x, hxf, hxo⟩ 

noncomputable def Ψ : Solution' p → Solution p := 
  fun s => 
    let x := Classical.choose s
    let ⟨hxf, hxo⟩ := Classical.choose_spec s
    ⟨x, hxf, hxo⟩
