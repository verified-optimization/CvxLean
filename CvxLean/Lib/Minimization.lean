import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Function

/-- Type of an optimization problem. -/
structure Minimization (D : Type) (R : Type) where 
  objFun : D → R
  constraints : D → Prop

namespace Minimization

variable {D E R S : Type} [Preorder R] [Preorder S] 
variable (p : Minimization D R) (q : Minimization E R)

/-- A feasible point is a point in the domain that satisfies the constraints. -/
structure FeasPoint where 
  point : D 
  feasibility : p.constraints point

/-- A solution is a feasible point that is also optimal. -/
structure Solution where 
  point : D 
  feasibility : p.constraints point 
  optimality : ∀ y : p.FeasPoint, p.objFun point ≤ p.objFun y.point

section Reductions

/-- Reduction from solution to solution maintaining equivalence through 
functions `f` and `g`. For most purposes, this might be enough. -/
def simple_reduction
  (sol : q.Solution)
  (f : D → E) (g : E → D)
  (h_objFun_f : ∀ {x : D}, p.constraints x → q.objFun (f x) ≤ p.objFun x)
  (h_objFun_g : ∀ {x : E}, q.constraints x → p.objFun (g x) ≤ q.objFun x)
  (h_constraints_f : ∀ {x}, p.constraints x → q.constraints (f x))
  (h_constraints_g : ∀ {x}, q.constraints x → p.constraints (g x)) :
  p.Solution :=
  { point := g sol.point,
    feasibility := h_constraints_g sol.feasibility,
    optimality := by
      intro xhx
      cases xhx with
      | mk x hx =>
        apply le_trans _ (h_objFun_f hx)
        apply le_trans (h_objFun_g sol.feasibility)
        exact sol.optimality {
          point := f x,
          feasibility := h_constraints_f hx } }

/-- Decompose constraint by adding another equality constraint. -/
def decompose_constraint
  (g : D → E) (c : D → E → Prop)
  (hc : ∀ x, p.constraints x = c x (g x)) 
  (sol : Solution
    { objFun := fun (y : E × D) => objFun p y.snd, 
      constraints := fun (y : E × D) => y.fst = g y.snd ∧ c y.snd y.fst }) :
  p.Solution := 
simple_reduction p _ sol
  (fun x => (g x, x)) (fun x => x.2)
  (fun {x} hx => le_refl _)
  (fun {x} hx => le_refl _)
  (fun {x} hx => ⟨rfl, (hc _) ▸ hx⟩)
  (fun {x} hx => by {rw [hc, ←hx.1]; exact hx.2})

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
  (fun hx => by simp [Function.comp])
  (fun hx => by simp)
  (fun {x} hx => by simp [Function.comp]; exact hx)
  (fun {x} hx => by simp; exact hx)

/-- -/
def map_objective {D : Type}
  (R S : Type) [Preorder R] [Preorder S]
  (f : D → R) (g : R → S) (cs : D → Prop)
  (hg: ∀ r s, cs r → cs s → g (f r) ≤ g (f s) → f r ≤ f s)
  (sol : Solution
    { objFun := g ∘ f,
      constraints := cs }) :
Solution
  { objFun := f,
    constraints := cs } :=
{ point := sol.point,
  feasibility := sol.feasibility,
  optimality := by
    intros y
    have : g (f sol.point) ≤ g (f y.point) := sol.optimality ⟨y.1, y.2⟩
    exact hg _ _ sol.feasibility y.feasibility this }

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
  (fun {x} hx => by simp)
  (fun {x} hx => by simp [hfg x hx, hx]; exact hx)
  (fun {x} hx => hx)

/-- -/
def rewrite_objective {cs : D → Prop}
{f : D → R}
{g : D → R}
(hfg : ∀ x, cs x → f x = g x)
(sol : Solution
    { objFun := g
      constraints := cs })  :
Solution {objFun := f, constraints := cs} :=
simple_reduction _ _ sol id id
  (fun {x} hx => le_of_eq (hfg x hx).symm)
  (fun {x} hx => le_of_eq (hfg x hx))
  (fun {x} hx => hx)
  (fun {x} hx => hx)

/-- -/
def rewrite_constraints {cs : D → Prop}
  {f : D → R}
  (hfg : ∀ x, cs x ↔ ds x)
  (sol : Solution { objFun := f, constraints := ds }) :
  Solution {objFun := f, constraints := cs} := by
  have := funext fun x => (propext (hfg x))
  simpa [this]

def rewrite_constraint_1 {R D} [Preorder R] {c1 c1' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc1 : ∀ x, c1 x ↔ c1' x)
  (sol : Solution { objFun := f, constraints := fun x => c1' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ cs x  } :=
  rewrite_constraints (fun x => by rw [hc1]) sol

def rewrite_constraint_2 {R D} [Preorder R] {c1 c2 c2' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc2 : ∀ x, c2 x ↔ c2' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc2]) sol

def rewrite_constraint_3 {R D} [Preorder R] {c1 c2 c3 c3' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc3 : ∀ x, c3 x ↔ c3' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc3]) sol

def rewrite_constraint_4 {R D} [Preorder R] {c1 c2 c3 c4 c4' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc4 : ∀ x, c4 x ↔ c4' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc4]) sol

def rewrite_constraint_5 {R D} [Preorder R] {c1 c2 c3 c4 c5 c5' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc5 : ∀ x, c5 x ↔ c5' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc5]) sol

def rewrite_constraint_6 {R D} [Preorder R] {c1 c2 c3 c4 c5 c6 c6' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc6 : ∀ x, c6 x ↔ c6' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc6]) sol

def rewrite_constraint_7 {R D} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c7' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc7 : ∀ x, c7 x ↔ c7' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc7]) sol

def rewrite_constraint_8 {R D} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c8' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc8 : ∀ x, c8 x ↔ c8' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc8]) sol

def rewrite_constraint_9 {R D} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c9' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc9 : ∀ x, c9 x ↔ c9' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc9]) sol

def rewrite_constraint_10 {R D} [Preorder R] {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c10' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hc10 : ∀ x, c10 x ↔ c10' x)
  (sol : Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10' x ∧ cs x }) :
  Solution { objFun := f, constraints := fun x => c1 x ∧ c2 x ∧ c3 x ∧ c4 x ∧ c5 x ∧ c6 x ∧ c7 x ∧ c8 x ∧ c9 x ∧ c10 x ∧ cs x } :=
  rewrite_constraints (fun x => by rw [hc10]) sol

def rewrite_constraint_last {R D} [Preorder R] {cl cl' : D → Prop} {cs : D → Prop}
  {f : D → R}
  (hcl : ∀ x, cl x ↔ cl' x)
  (sol : Solution { objFun := f, constraints := fun x => cs x ∧ cl' x }) :
  Solution { objFun := f, constraints := fun x => cs x ∧ cl x } :=
  rewrite_constraints (fun x => by rw [hcl]) sol

-- example : Solution $ 
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to 
--       h1 : x <= 1
--       h2 : x <= 0 := by 
--   have h : ∀ x : ℝ, x <= 1 ↔ x <= 2 - 1 := sorry 
--   apply @rewrite_constraint1 ℝ ℝ _ _ _ _ _ h
--   sorry

end Reductions

end Minimization
