import CvxLean.Tactic.DCP.Atoms
import CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones
import CvxLean.Tactic.DCP.AtomLibrary.Fns.VecCons

namespace CvxLean

open Real

declare_atom sq [convex] (x : ℝ)? : x ^ 2 :=
vconditions
implementationVars (t : ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : rotatedSoCone t (1/2) ![x])
solution
  (t := x ^ 2)
solutionEqualsAtom rfl
feasibility
  (c1 : by
    unfold rotatedSoCone
    simp
    exact ⟨sq_nonneg x, zero_le_two⟩)
optimality by
  unfold rotatedSoCone at c1
  have h := c1.1
  simp at h ⊢
  exact h
vconditionElimination

-- TODO: There is an issue matching functions so we need to wrap it.
def test (x : (Fin n) → ℝ) := fun i => ![x i]

declare_atom vecCons2 [affine] (n : Nat)& (x : (Fin n) → ℝ)? :
  test x :=
bconditions
homogenity by
  unfold test
  ext i
  simp
additivity by
  unfold test
  ext i
  simp
optimality le_refl _

declare_atom Vec.sq [convex] (n : ℕ)& (x : Fin n → ℝ)? : x ^ 2 :=
vconditions
implementationVars (t : Fin n → ℝ)
implementationObjective (t)
implementationConstraints
  (c1 : Vec.rotatedSoCone t (fun _ => 1/2) (test x))
solution
  (t := x ^ 2)
solutionEqualsAtom rfl
feasibility
  (c1 : by
    unfold Vec.rotatedSoCone
    intros t i
    convert sq.feasibility0 (x i); simp)
optimality by
  intros i
  unfold Vec.rotatedSoCone at c1
  convert sq.optimality (x i) (t i) (c1 i); simp
vconditionElimination

end CvxLean
