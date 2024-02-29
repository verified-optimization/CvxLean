import CvxLean.Tactic.DCP.AtomCmdimport CvxLean.Tactic.DCP.AtomLibrary.Sets.Cones

namespace CvxLean

-- -- Convex
-- class IsRealAtom (f : ℝ → ℝ) where
--   (impObj : ℝ × ℝ → ℝ)
--   (impObjAffine : ∀ (x : ℝ) (t : ℝ) (s : ℝ), s * impObj ⟨x, t⟩ = impObj ⟨s * x, s * t⟩)
--   (impConstr : ℝ × ℝ → Prop)
--   (sol : ℝ → ℝ)
--   (solEqAtom : ∀ (x : ℝ), impObj ⟨x, sol x⟩ = f x)
--   (feasibility : ∀ (x : ℝ), impConstr ⟨x, sol x⟩)
--   (optimality : ∀ (x : ℝ) (t : ℝ), impConstr ⟨x, t⟩ → f x ≤ impObj ⟨x, t⟩)

-- declare_atom IsSimpleRealAtom.impConstr [cone] (f : ℝ → ℝ)? (hatom : IsRealAtom f)? (x : ℝ)? (t : ℝ)? (s : ℝ)? : hatom.impConstr ⟨x / s, t / s⟩ :=
-- optimality le_refl _

-- declare_atom IsSimpleRealAtom.impObj [convex] (f : ℝ → ℝ)? (hatom : IsRealAtom f)? (x : ℝ)? (t : ℝ)? (s : ℝ)? : hatom.impObj ⟨x, t⟩ :=
-- vconditions
-- implementationVars (z : ℝ)
-- implementationObjective sorry
-- implementationConstraints
--   (c : True)
-- solution (z := sorry)
-- solutionEqualsAtom sorry
-- feasibility
--   (c : trivial)
-- optimality by
--   sorry
-- vconditionElimination

-- #check EuclideanDomain.mul_div_cancel_left

-- -- IsConvexReducible?

-- Another option: declare_atom_unsafe, and do everything in meta.

-- declare_atom perspective [convex] (f : ℝ → ℝ)? (x : ℝ)? (hatom : IsRealAtom f)? (s : ℝ)? : s * f (x / s) :=
-- vconditions (cond : 0 < s)
-- implementationVars (t : ℝ)
-- implementationObjective (hatom.impObj ⟨x, t⟩)
-- implementationConstraints
--   (c : hatom.impConstr ⟨x / s, t / s⟩)
--   (cs : 0 < s)
-- solution (t := s * hatom.sol (x / s))
-- solutionEqualsAtom by {
--   simp
--   sorry
-- }
-- feasibility
--   (c : by {
--     dsimp
--     simp [mul_div_cancel_left (a := s) (hatom.sol (x / s)) (ne_of_lt cond).symm]
--     exact hatom.feasibility (x / s)
--   })
--   (cs : cond)
-- optimality by {
--     have := hatom.optimality (x / s) (t / s) c
--     sorry
--   }
-- vconditionElimination
--   (cond : cs)

-- declare_atom perspective [convex] (f : ℝ → ℝ)? (x : ℝ)? (s : ℝ)? : s * f (x / s) :=
-- vconditions (cond : 0 < s)
-- implementationVars (t : ℝ)
-- implementationObjective t + 34
-- implementationConstraints
--   (cs : 0 < s)
-- solution (t := 0)
-- solutionEqualsAtom by
--   sorry
-- feasibility
--   (cs : cond)
-- optimality by
--   sorry
-- vconditionElimination
--   (cond : cs)


-- example : Minimization.Solution <|
--   optimization (x : ℝ)
--     minimize (2 * Real.exp (x / 2))
--     subject to
--       h : Real.posOrthCone x := by
--     dcp

end CvxLean
