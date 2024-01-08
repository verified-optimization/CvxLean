import CvxLean.Lib.Minimization

/-!
# Reduction
-/

variable {D E R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R)

abbrev Reduction := q.Solution → p.Solution

namespace Reduction

/-- Decompose constraint by adding another equality constraint. -/
def decompose_constraint
    (g : D → E) (c : D → E → Prop)
    (hc : ∀ x, p.constraints x = c x (g x))
    (sol : Solution
      { objFun := fun (y : E × D) => objFun p y.snd,
        constraints := fun (y : E × D) => y.fst = g y.snd ∧ c y.snd y.fst }) :
    p.Solution :=
  simple_reduction _ sol (fun x => (g x, x)) (fun x => x.2)
    (fun {_} _ => le_refl _)
    (fun {_} _ => le_refl _)
    (fun {_} hx => ⟨rfl, (hc _) ▸ hx⟩)
    (fun {_} hx => (hc _).symm ▸ hx.1 ▸ hx.2)

/-- -/
def eq_to_le_left
  (e: Equiv D (S × E)) (f : E → S) (c : D → Prop)
  (hc : ∀ {x}, p.constraints x ↔ ((e.toFun x).1 = f (e.toFun x).2 ∧ c x))
  (h_objFun : ∀ x r s, p.objFun (e.symm.toFun (r,x)) = p.objFun (e.symm.toFun (s,x)))
  (h_mono: ∀ x r s, r ≤ s → c (e.symm.toFun (r, x)) → c (e.symm.toFun (s, x)))
  (sol : Solution
    { objFun := p.objFun,
      constraints := fun x => (e.toFun x).1 ≤ f (e.toFun x).2 ∧ c x } ) :
  p.Solution :=
simple_reduction p _ sol
  (fun x => x) (fun x => e.symm.toFun ⟨f (e.toFun x).2, (e.toFun x).2⟩)
  (fun {x} hx => le_refl _)
  (fun {x} hx => by
    rw [h_objFun _ _ ((e.toFun x).1)]
    simp [le_of_eq])
  (fun {x} hx => ⟨le_of_eq (hc.1 hx).1, (hc.1 hx).2⟩)
  (fun {x} hx => by
    have : c (e.symm.toFun (f (e.toFun x).2, (e.toFun x).2)) := by
      apply h_mono
      apply hx.1
      simp [hx.2]
    simp_all )

/-- -/
def eq_to_le_right
  (e: Equiv D (S × E)) (f : E → S) (c : D → Prop)
  (hc : ∀ {x}, p.constraints x ↔ (f (e.toFun x).2 = (e.toFun x).1 ∧ c x))
  (h_objFun : ∀ x r s, p.objFun (e.symm.toFun ⟨r, x⟩) = p.objFun (e.symm.toFun ⟨s, x⟩))
  (h_mono: ∀ x r s, r ≤ s → c (e.symm.toFun (s, x)) → c (e.symm.toFun ⟨r, x⟩))
  (sol : Solution
    { objFun := p.objFun,
      constraints := fun x => f (e.toFun x).2 ≤ (e.toFun x).1 ∧ c x }) :
  p.Solution :=
simple_reduction p _ sol
  (fun x => x) (fun x => e.symm.toFun ⟨f (e.toFun x).2, (e.toFun x).2⟩)
  (fun {x} hx => le_refl _)
  (fun {x} hx => by
    rw [h_objFun _ _ ((e.toFun x).1)]
    simp [le_of_eq])
  (fun {x} hx => ⟨le_of_eq (hc.1 hx).1, (hc.1 hx).2⟩)
  (fun {x} hx => by
    have : c (e.symm.toFun (f (e.toFun x).2, (e.toFun x).2)) := by
      apply h_mono
      apply hx.1
      simp [hx.2]
    simp_all)

/-- -/
def linearization_mono {of : D → R} {cs : D → Prop}
  {S : Type}
  {g : D → S} {c : S → D → Prop} {f : S → D → R}
  {hS : Preorder S}
  (hof : ∀ x, of x = f (g x) x)
  (hcs : ∀ x, cs x = c (g x) x)
  (h_mono_of: ∀ x r s, r ≤ s → f s x ≤ f r x)
  (h_mono_cs: ∀ x r s, r ≤ s → c r x → c s x)
  (sol : Solution
      { objFun := fun (y : S × D) => f y.1 y.2,
        constraints := fun y => y.1 ≤ g y.2 ∧ c y.1 y.2 }) :
  Solution {objFun := of, constraints := cs} :=
simple_reduction _ _ sol
  (fun x => (g x, x)) (fun x => x.2)
  (fun {x} hx => le_of_eq (hof _).symm)
  (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ hx.1)
  (fun {x} hx => by simp only [hcs] at hx; exact ⟨le_refl _, hx⟩)
  (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ hx.1 hx.2)

/-- -/
def linearization_antimono {of : D → R} {cs : D → Prop}
  {S : Type}
  {g : D → S} {c : S → D → Prop} {f : S → D → R}
  {hS : Preorder S}
  (hof : ∀ x, of x = f (g x) x)
  (hcs : ∀ x, cs x = c (g x) x)
  (h_mono_of: ∀ x r s, r ≤ s → f r x ≤ f s x)
  (h_mono_cs: ∀ x r s, r ≤ s → c s x → c r x)
  (sol : Solution
      { objFun := fun (y : S × D) => f y.1 y.2,
        constraints := fun y => g y.2 ≤ y.1 ∧ c y.1 y.2 }) :
  Solution {objFun := of, constraints := cs} :=
simple_reduction _ _ sol
  (fun x => (g x, x)) (fun x => x.2)
  (fun {x} hx => le_of_eq (hof _).symm)
  (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ hx.1)
  (fun {x} hx => by simp only [hcs] at hx; exact ⟨le_refl _, hx⟩)
  (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ hx.1 hx.2)

/-- -/
def graph_expansion_greatest {of : D → R} {cs : D → Prop}
  {S : Type}
  {g : D → S} {c d : S → D → Prop} {f : S → D → R}
  {hS : Preorder S}
  (hg : ∀ x v, c v x → IsGreatest {y | d y x} (g x))
  (hof : ∀ x, of x = f (g x) x)
  (hcs : ∀ x, cs x = c (g x) x)
  (h_mono_of: ∀ x r s, r ≤ s → f s x ≤ f r x)
  (h_mono_cs: ∀ x r s, r ≤ s → c r x → c s x)
  (sol : Solution
      { objFun := fun (y : S × D) => f y.1 y.2,
        constraints := fun (y : S × D) => d y.1 y.2 ∧ c y.1 y.2 })  :
  Solution {objFun := of, constraints := cs} :=
simple_reduction _ _ sol
  (fun x => (g x, x)) (fun x => x.2)
  (fun hx => le_of_eq (hof _).symm)
  (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1))
  (fun {x} hx => by simp only [hcs] at hx; exact ⟨(hg x (g x) hx).1, hx⟩)
  (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1) hx.2)

/-- -/
def graph_expansion_least {of : D → R} {cs : D → Prop}
  {S : Type}
  {g : D → S} {c d : S → D → Prop} {f : S → D → R}
  {hS : Preorder S}
  (hg : ∀ x v, c v x → IsLeast {y | d y x} (g x))
  (hof : ∀ x, of x = f (g x) x)
  (hcs : ∀ x, cs x = c (g x) x)
  (h_mono_of: ∀ x r s, r ≤ s → f r x ≤ f s x)
  (h_mono_cs: ∀ x r s, r ≤ s → c s x → c r x)
  (sol : Solution
      { objFun := fun (y : S × D) => f y.1 y.2,
        constraints := fun (y : S × D) => d y.1 y.2 ∧ c y.1 y.2 })  :
  Solution {objFun := of, constraints := cs} :=
simple_reduction _ _ sol
  (fun x => (g x, x)) (fun x => x.2)
  (fun hx => le_of_eq (hof _).symm)
  (fun {x} hx => by simp only [hof]; exact h_mono_of x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1))
  (fun {x} hx => by simp only [hcs] at hx; exact ⟨(hg x (g x) hx).1, hx⟩)
  (fun {x} hx => by simp only [hcs]; exact h_mono_cs x.2 _ _ ((hg x.2 x.1 hx.2).2 hx.1) hx.2)

/-- TODO: This is probably better done in a tactic? -/
def graph_expansion_least_forall {of : D → R} {cs : D → Prop}
  {I S : Type} [Inhabited I]
  {g : D → I → S} {h : D → I → S} {c d : S → D → Prop}
  {hS : Preorder S}
  (hg : ∀ x v i, c v x → IsLeast {y | d y x} (g x i))
  (hcs : ∀ x, cs x = ∀ i, c (g x i) x)
  (h_mono_cs: ∀ x r s, r ≤ s → c s x → c r x)
  (sol : Solution
      { objFun := fun (y : (I → S) × D) => of y.2,
        constraints := fun (y : (I → S) × D) => (∀ i, d (y.1 i) y.2) ∧ (∀ i, c (y.1 i) y.2) })  :
  Solution {objFun := of, constraints := cs} :=
  @graph_expansion_least D R _ of cs (I → S) g
    (fun y x => ∀ i, c (y i) x)
    (fun y x => ∀ i, d (y i) x)
    (fun y x => of x)
    ⟨fun a i => le_refl (a i),
     fun a b c hab hbc i => le_trans (hab i) (hbc i),
     fun a b => Iff.refl _⟩
    (fun x v hc => ⟨fun i => (hg x (v i) i (hc i)).1,
     fun v' c i => (hg x (v i) i (hc i)).2 (c i)⟩)
    (fun x => rfl)
    hcs
    (fun x r s hrs => le_refl _)
    (fun x r s hrs hc i => h_mono_cs x (r i) (s i) (hrs i) (hc i))
    sol

/-- Change domain to equivalent type. -/
noncomputable def domain_equiv {D E : Type} (e : Equiv E D)
  (R : Type) [Preorder R]
  (f : D → R) (cs : D → Prop)
  (sol : Solution
    { objFun := f ∘ e.toFun,
      constraints := cs ∘ e.toFun}) :
Solution
  { objFun := f,
    constraints := cs } :=
simple_reduction _ _ sol e.symm.toFun e.toFun
  (fun _ => by simp [Function.comp])
  (fun _ => by simp)
  (fun {x} hx => by simp [Function.comp]; exact hx)
  (fun {x} hx => by simp; exact hx)

section Maps

/-- -/
def map_objective {D : Type}
    (R S : Type) [Preorder R] [Preorder S]
    (f : D → R) (g : R → S) (cs : D → Prop)
    (hg : ∀ r s, cs r → cs s → g (f r) ≤ g (f s) → f r ≤ f s)
    (sol : Solution { objFun := g ∘ f, constraints := cs }) :
    Solution { objFun := f, constraints := cs } :=
  { point := sol.point,
    feasibility := sol.feasibility,
    optimality := by
      intros y hy
      have : g (f sol.point) ≤ g (f y) := sol.optimality y hy
      exact hg _ _ sol.feasibility hy this }

/-- -/
def map_domain {of : D → R} {cs : D → Prop}
{f : D → E}
{g : E → D}
(hfg : ∀ x, cs x → g (f x) = x)
(sol : Solution
    { objFun := of ∘ g
      constraints := cs ∘ g })  :
Solution {objFun := of, constraints := cs} :=
simple_reduction _ _ sol f g
  (fun {x} hx => by simp [hfg x hx])
  (fun {x} _  => by simp)
  (fun {x} hx => by simp [hfg x hx, hx]; exact hx)
  (fun {x} hx => hx)

end Maps


section Rewrites

def rewrite_objective {D R} [Preorder R] {f g : D → R} {cs : D → Prop}
  (hrw : ∀ x, cs x → f x = g x)
  (sol : Solution { objFun := g, constraints := cs }) :
  Solution { objFun := f, constraints := cs } :=
  simple_reduction _ _ sol id id
    (fun {x} hx => le_of_eq (hrw x hx).symm)
    (fun {x} hx => le_of_eq (hrw x hx))
    (fun {_} hx => hx)
    (fun {_} hx => hx)

def rewrite_constraints {D R} [Preorder R] {cs ds : D → Prop} {f : D → R}
  (hrw : ∀ x, cs x ↔ ds x)
  (sol : Solution { objFun := f, constraints := ds }) :
  Solution { objFun := f, constraints := cs } := by
  have := funext fun x => (propext (hrw x))
  simpa [this]

def rewrite_constraint_1 {D R} [Preorder R] {c1 c1' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, cs x → (c1 x ↔ c1' x))
  (sol : Solution { objFun := f, constraints := fun x => c1' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ cs x  } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.2] at hx; exact hx)

def rewrite_constraint_1_last {D R} [Preorder R] {c1 c1' : D → Prop} {f : D → R}
  (hrw : ∀ x, (c1 x ↔ c1' x))
  (sol : Solution { objFun := f, constraints := fun x => c1' x }) :
  Solution { objFun := f, constraints := fun x => c1 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x] at hx; exact hx)

def rewrite_constraint_2 {D R} [Preorder R] {c1 c2 c2' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → cs x → (c2 x ↔ c2' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.2] at hx; exact hx)

def rewrite_constraint_2_last {D R} [Preorder R] {c1 c2 c2' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → (c2 x ↔ c2' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1] at hx; exact hx)

def rewrite_constraint_3 {D R} [Preorder R] {c1 c2 c3 c3' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → cs x → (c3 x ↔ c3' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.2] at hx; exact hx)

def rewrite_constraint_3_last {D R} [Preorder R] {c1 c2 c3 c3' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → (c3 x ↔ c3' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1] at hx; exact hx)

def rewrite_constraint_4 {D R} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → cs x → (c4 x ↔ c4' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2] at hx; exact hx)

def rewrite_constraint_4_last {D R} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → (c4 x ↔ c4' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1] at hx; exact hx)

def rewrite_constraint_5 {D R} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → cs x → (c5 x ↔ c5' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.2] at hx; exact hx)

def rewrite_constraint_5_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → (c5 x ↔ c5' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1] at hx; exact hx)

def rewrite_constraint_6 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → cs x → (c6 x ↔ c6' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.2] at hx; exact hx)

def rewrite_constraint_6_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → (c6 x ↔ c6' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1] at hx; exact hx)

def rewrite_constraint_7 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → cs x → (c7 x ↔ c7' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.2] at hx; exact hx)

def rewrite_constraint_7_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → (c7 x ↔ c7' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1] at hx; exact hx)

def rewrite_constraint_8 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → cs x → (c8 x ↔ c8' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2] at hx; exact hx)

def rewrite_constraint_8_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → (c8 x ↔ c8' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1] at hx; exact hx)

def rewrite_constraint_9 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → cs x → (c9 x ↔ c9' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2] at hx; exact hx)

def rewrite_constraint_9_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → (c9 x ↔ c9' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1] at hx; exact hx)

def rewrite_constraint_10 {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {cs : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → cs x → (c10 x ↔ c10' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10 x ∧ cs x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.2.2] at hx; exact hx)

def rewrite_constraint_10_last {D R} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {f : D → R}
  (hrw : ∀ x, c1 x → c2 x → c3 x → c4 x → c5 x → c6 x → c7 x → c8 x → c9 x → (c10 x ↔ c10' x))
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10 x } :=
  simple_reduction _ _ sol id id
    (fun {x} _ => le_refl _)
    (fun {x} _ => le_refl _)
    (fun {x} hx => by simp only [hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1] at hx; exact hx)
    (fun {x} hx => by simp only [←hrw x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1] at hx; exact hx)

end Rewrites

end Reduction
