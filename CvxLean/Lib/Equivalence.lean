import CvxLean.Lib.Minimization 
import CvxLean.Tactic.DCP.AtomLibrary

attribute [-instance] coeDecidableEq
attribute [-simp] Set.inj_on_empty Set.inj_on_singleton Quot.lift_on₂_mk 
  Quot.lift_on_mk Quot.lift₂_mk

open Minimization

variable {R D E F : Type} [Preorderₓ R]
variable (p : Minimization D R) (q : Minimization E R) (r : Minimization F R)
/-
  p := min { f(x) | c_p(x) }
  q := min { g(x) | c_q(x) }
  r := min { h(x) | c_r(x) }
-/

structure MinEquiv where 
  phi : D → E
  psi : E → D
  phi_feasibility : ∀ x, p.constraints x → q.constraints (phi x)
  phi_optimality : ∀ x, p.constraints x → q.objFun (phi x) ≤ p.objFun x
  psi_feasibility : ∀ y, q.constraints y → p.constraints (psi y)
  psi_optimality : ∀ y, q.constraints y → p.objFun (psi y) ≤ q.objFun y

def MinEquiv.toFwd (E : MinEquiv p q) : Solution p → Solution q := 
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
      exact le_transₓ (le_transₓ h₁ h₂) h₃
  }

def MinEquiv.toBwd (E : MinEquiv p q) : Solution q → Solution p := 
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
      exact le_transₓ (le_transₓ h₁ h₂) h₃
  }

def MinEquiv.refl : MinEquiv p p := 
  { phi := id, 
    psi := id,
    phi_feasibility := fun _ hx => hx,
    phi_optimality := fun _ _ => le_reflₓ _,
    psi_feasibility := fun _ hy => hy,
    psi_optimality := fun _ _ => le_reflₓ _ }

def MinEquiv.symm (E : MinEquiv p q) : MinEquiv q p := 
  { phi := E.psi, 
    psi := E.phi,
    phi_feasibility := E.psi_feasibility,
    phi_optimality := E.psi_optimality,
    psi_feasibility := E.phi_feasibility,
    psi_optimality := E.phi_optimality }

def MinEquiv.trans (E₁ : MinEquiv p q) (E₂ : MinEquiv q r) : 
  MinEquiv p r := 
  { phi := E₂.phi ∘ E₁.phi,
    psi := E₁.psi ∘ E₂.psi,
    phi_feasibility := fun x hx =>
      E₂.phi_feasibility (E₁.phi x) (E₁.phi_feasibility x hx),
    phi_optimality := fun x hx => by
      -- h(phi₂(phi₁(x))) <= g(phi₁(x))
      have h₁ := E₂.phi_optimality (E₁.phi x) (E₁.phi_feasibility x hx);
      -- g(phi₁(x)) <= f(x)
      have h₂ := E₁.phi_optimality x hx;
      exact le_transₓ h₁ h₂,
    psi_feasibility := fun y hy =>
      E₁.psi_feasibility (E₂.psi y) (E₂.psi_feasibility y hy),
    psi_optimality := fun y hy => by 
      -- f(psi₁(psi₂(y))) <= g(psi₂(y))
      have h₁ := E₁.psi_optimality (E₂.psi y) (E₂.psi_feasibility y hy);
      -- g(psi₂(y)) <= h(y)
      have h₂ := E₂.psi_optimality y hy;
      exact le_transₓ h₁ h₂
  }

instance : 
  Trans (@MinEquiv R D E _) (@MinEquiv R E F _) (@MinEquiv R D F _) := 
  { trans := fun E₁ E₂ => MinEquiv.trans _ _ _ E₁ E₂ }

-- NOTE: B for bundled. 

structure MinimizationB := 
  (D : Type)
  (prob : Minimization D Real)

def MinimizationB.equiv : MinimizationB → MinimizationB → Prop := 
  fun p q => Nonempty (MinEquiv p.prob q.prob)

lemma MinimizationB.equiv_refl (p : MinimizationB) : 
  MinimizationB.equiv p p :=
  ⟨MinEquiv.refl _⟩

lemma Minimization.equiv_symm {p q : MinimizationB} : 
  MinimizationB.equiv p q → MinimizationB.equiv q p :=
  fun ⟨E⟩ => ⟨@MinEquiv.symm Real p.D q.D _ p.prob q.prob E⟩ 

lemma Minimization.equiv_trans {p q r : MinimizationB} : 
  MinimizationB.equiv p q → MinimizationB.equiv q r → MinimizationB.equiv p r :=
  fun ⟨E₁⟩ ⟨E₂⟩ => 
    ⟨@MinEquiv.trans Real p.D q.D r.D _ p.prob q.prob r.prob E₁ E₂⟩   

instance : Setoid MinimizationB := 
  { r := MinimizationB.equiv,
    iseqv := 
      { refl := MinimizationB.equiv_refl, 
        symm := Minimization.equiv_symm, 
        trans := Minimization.equiv_trans } }

-- NOTE: Q for quotient.

def MinimizationQ := @Quotient MinimizationB (by infer_instance)

def MinimizationQ.mk {D : Type} (p : Minimization D Real) : MinimizationQ := 
  Quotient.mk' { D := D, prob := p }

syntax "{|" term "|}" : term

macro_rules 
  | `({| $p:term |}) => do pure (← `(@MinimizationQ.mk _ $p)).raw

def MinimizationQ.constraints_comm
  {D : Type} {f : D → Real} {cs₁ cs₂ : D → Prop} :
  {| { objFun := f, constraints := fun x => cs₁ x ∧ cs₂ x } |} = 
  {| { objFun := f, constraints := fun x => cs₂ x ∧ cs₁ x } |} := by
  apply Quotient.sound; apply Nonempty.intro; exact 
  { phi := id, 
    psi := id,
    phi_feasibility := fun _ hx => And.comm.mp hx,
    phi_optimality := fun _ _ => le_reflₓ _,
    psi_feasibility := fun _ hy => And.comm.mp hy,
    psi_optimality := fun _ _ => le_reflₓ _ }

-- Useful to have this.
def MinimizationQ.constraints_comm_l
  {D : Type} {f : D → Real} {cs cs₁ cs₂ : D → Prop} :
  {| { objFun := f, constraints := fun x => cs x ∧ (cs₁ x ∧ cs₂ x) } |} = 
  {| { objFun := f, constraints := fun x => cs x ∧ (cs₂ x ∧ cs₁ x) } |} :=
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun _ hx => ⟨hx.1, And.comm.mp hx.2⟩,
    phi_optimality := fun _ _ => le_reflₓ _,
    psi_feasibility := fun _ hy => ⟨hy.1, And.comm.mp hy.2⟩,
    psi_optimality := fun _ _ => le_reflₓ _ }

def MinimizationQ.constraints_assoc 
  {D : Type} {f : D → Real} {cs₁ cs₂ cs₃ : D → Prop} :
  {| { objFun := f, constraints := fun x => (cs₁ x ∧ cs₂ x) ∧ cs₃ x } |} = 
  {| { objFun := f, constraints := fun x => cs₁ x ∧ (cs₂ x ∧ cs₃ x) } |} := 
  Quotient.sound <| Nonempty.intro <|
  { phi := id, 
    psi := id,
    phi_feasibility := fun _ hx => And.assoc.mp hx,
    phi_optimality := fun _ _ => le_reflₓ _,
    psi_feasibility := fun _ hy => And.assoc.mpr hy,
    psi_optimality := fun _ _ => le_reflₓ _ }


section QuotientExample 

open CvxLean MinimizationQ

example :
  {| optimization (x : Real) minimize x subject to h : 0 < x ∧ True ∧ False |} =
  {| optimization (x : Real) minimize x subject to h : False ∧ True ∧ 0 < x |} := by
  rw [constraints_comm_l (cs₁ := fun _ => True)]
  rw [constraints_comm]
  rw [constraints_assoc]

end QuotientExample


section Example

noncomputable def MinEquiv.map_domain_exp
  {f : Real → Real} {cs : Real → Prop} : 
  MinEquiv 
    { objFun := f, constraints := fun x => 0 < x ∧ cs x } 
    { objFun := f ∘ Real.exp, constraints := fun x => 0 < Real.exp x ∧ cs (Real.exp x) } := 
  { phi := Real.log,
    psi := Real.exp,
    phi_feasibility := fun x hx => by 
      simp only [constraints, Function.comp] at hx ⊢;
      rw [Real.exp_log hx.1]
      exact ⟨hx.1, hx.2⟩,
    phi_optimality := fun x hx => by
      simp only [objFun, constraints, Function.comp] at hx ⊢;
      rw [Real.exp_log hx.1]
      exact le_reflₓ _,
    psi_feasibility := fun x hx => hx -- by 
      -- simp only [constraints, Function.comp] at hx ⊢;
      -- exact hx -- ⟨Real.exp_pos _, hx⟩,
    psi_optimality := fun x hx => by
      --simp only [objFun, constraints, Function.comp] at hx ⊢;
      exact le_reflₓ _
  }

-- noncomputable def MinEquiv.add_exp_pos 
--   {f : Real → Real} {cs : Real → Prop} :
--   MinEquiv 
--     { objFun := f, constraints := cs } 
--     { objFun := f, constraints := fun x => 0 < Real.exp x ∧ cs x } :=
--   { phi := id,
--     psi := id, 
--     phi_feasibility := fun x hx => by
--       simp only [constraints, Function.comp] at hx ⊢;
--       exact ⟨Real.exp_pos _, hx⟩,
--     phi_optimality := fun x _ => le_reflₓ _,
--     psi_feasibility := fun x hx => by
--       simp only [constraints, Function.comp] at hx ⊢;
--       exact hx.2,
--     psi_optimality := fun x _ => le_reflₓ _
--   }

noncomputable def MinEquiv.log_le_log
  {f : Real → Real} {cs : Real → Prop} {g h : Real → Real} :
  MinEquiv 
    { objFun := f, 
      constraints := fun x => 0 < g x ∧ 0 < h x ∧ g x ≤ h x ∧ cs x }
    { objFun := f, 
      constraints := fun x => 0 < g x ∧ 0 < h x ∧ Real.log (g x) ≤ Real.log (h x) ∧ cs x } :=
  { phi := id, 
    psi := id, 
    phi_feasibility := fun x hx => by
      simp only [constraints, Function.comp] at hx ⊢;
      exact ⟨hx.1, hx.2.1, (Real.log_le_log hx.1 hx.2.1).2 hx.2.2.1, hx.2.2.2⟩,
    phi_optimality := fun x _ => le_reflₓ _,
    psi_feasibility := fun x hx => by
      simp only [constraints, Function.comp] at hx ⊢;
      exact ⟨hx.1, hx.2.1, (Real.log_le_log hx.1 hx.2.1).1 hx.2.2.1, hx.2.2.2⟩,
    psi_optimality := fun x _ => le_reflₓ _
  }

noncomputable def MinEquiv.rewrite_constraints 
  {f : D → R} {cs ds : D → Prop}
  (hcsds : ∀ x, cs x ↔ ds x) : 
  MinEquiv 
    { objFun := f, constraints := cs } 
    { objFun := f, constraints := ds } :=
  { phi := id,
    psi := id, 
    phi_feasibility := fun x hx => by
      simp only [constraints, Function.comp] at hx ⊢;
      exact (hcsds x).1 hx
    phi_optimality := fun x _ => le_reflₓ _,
    psi_feasibility := fun x hx => by
      simp only [constraints, Function.comp] at hx ⊢;
      exact (hcsds x).2 hx
    psi_optimality := fun x _ => le_reflₓ _
  }

noncomputable def MinEquiv.rewrite_objective 
  {f : D → R}
  {g : D → R}
  (hfg : ∀ x, cs x → f x = g x) :
  MinEquiv 
    { objFun := f, constraints := cs } 
    { objFun := g, constraints := cs } :=
  { phi := id,
    psi := id,
    phi_feasibility := fun x hx => hx,
    phi_optimality := fun x hx => by dsimp; rw [hfg x hx]; exact le_reflₓ _,
    psi_feasibility := fun x hx => hx,
    psi_optimality := fun x hx => by dsimp; rw [hfg x hx]; exact le_reflₓ _
  }

noncomputable def MinEquiv.log_le_log_no_cs
  {f : Real → Real} {g h : Real → Real} :
  MinEquiv 
    { objFun := f, 
      constraints := fun x => 0 < g x ∧ 0 < h x ∧ g x ≤ h x }
    { objFun := f, 
      constraints := fun x => 0 < g x ∧ 0 < h x ∧ Real.log (g x) ≤ Real.log (h x) } :=
  MinEquiv.rewrite_constraints (fun x => by 
    exact ⟨
      fun h => ⟨h.1, h.2.1, (Real.log_le_log h.1 h.2.1).2 h.2.2⟩, 
      fun h => ⟨h.1, h.2.1, (Real.log_le_log h.1 h.2.1).1 h.2.2⟩⟩)  

open CvxLean

set_option pp.optMinimization false

noncomputable def calcTest : MinEquiv 
      (optimization (x : Real) 
        minimize x 
        subject to 
          h₁ : 0 < x 
          h₂ : 1 ≤ x)
      (optimization (x : Real)
        minimize Real.exp x
        subject to  
          h₁ : 0 < Real.exp x
          h : Real.log 1 ≤ Real.log (Real.exp x)) := by {
  calc 
    MinEquiv 
      (optimization (x : Real) 
        minimize x 
        subject to 
          h₁ : 0 < x 
          h₂ : 1 ≤ x)
      (optimization (x : Real) 
        minimize Real.exp x 
        subject to 
          h₁ : 0 < Real.exp x 
          h₂ : 1 ≤ Real.exp x):= by exact MinEquiv.map_domain_exp
    MinEquiv _ 
      (optimization (x : Real) 
        minimize Real.exp x 
        subject to 
          h₀ : 0 < (1 : Real)
          h₁ : 0 < Real.exp x
          h₂ : 1 ≤ Real.exp x) := by sorry -- exact MinEquiv.add_exp_pos 
    MinEquiv _ 
      (optimization (x : Real) 
        minimize Real.exp x 
        subject to 
          h₀ : 0 < (1 : Real)
          h₁ : 0 < Real.exp x
          h₂ : Real.log 1 ≤ Real.log (Real.exp x)) := by exact MinEquiv.log_le_log_no_cs
    -- MinEquiv _ 
    --   (optimization (x : Real) 
    --     minimize Real.exp (Real.exp x) 
    --     subject to 
    --       h : 1 ≤ Real.exp (Real.exp x)) := by refine MinEquiv.map_domain_exp
    }

end Example 

