import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.DCP.OC
import CvxLean.Tactic.DCP.AtomExt

/-!
# Types for DCP

This file gives names to the main structures used by the DCP procedure for better readability.
-/

namespace CvxLean

open Lean

namespace DCP

/- Atom data. -/

/-- Tree with all the atom data stored in the library. The leaves are just (affine or constant)
expressions. -/
abbrev GraphAtomDataTree := Tree GraphAtomData Expr


/- Arguments. -/

/-- This is the type of an argument. -/
abbrev Argument := Expr

/-- An atom may have several arguments. -/
abbrev Arguments := Array Argument

/-- Tree of the arguments of every atom unfolded (expressions at the nodes). -/
abbrev ArgumentsTree := Tree Arguments Unit


/- Curvature. -/

/-- Curvatures in the atom tree. -/
abbrev CurvatureTree := Tree Curvature Curvature


/- Background conditions. -/

/-- A background condition is just an expression of type `Prop`. -/
abbrev BCond := Expr

/-- An atom may have several background conditions. -/
abbrev BConds := Array BCond

/-- Background conditions of every atom in the atom tree. -/
abbrev BCondsTree := Tree BConds BConds


/- Result of finding an atom. -/

/-- Four trees: atom data tree, arguments tree, curvature tree, and background condition tree. -/
abbrev AtomDataTrees := GraphAtomDataTree × ArgumentsTree × CurvatureTree × BCondsTree


/- New variables and constraints. -/

/-- New variables introduced by every atom, as local declarations at the nodes. -/
abbrev NewVarsTree := Tree (Array LocalDecl) Unit

/-- Variables for the new constraints introduced by every atom, as local declarations at the
nodes. -/
abbrev NewConstrVarsTree := Tree (Array LocalDecl) Unit


/- New constraints (expressions). -/

/-- All the new constraints introduced by each atom, as expressions at the node. -/
abbrev NewConstrsTree := Tree (Array Expr) Unit


/- Variable condtions. -/

/-- In general a variable condition can either match a constraint exactly or it can be inferred from
the other constraints, we represent that as a sum type. If a number is given, then it is interpreted
as the index of the constraint that corresponds to the vcondition. -/
abbrev PreVCond := Nat ⊕ Expr

/- An atom may have several variable conditions. -/
abbrev PreVConds := Array PreVCond

/- All the vconditions for all the atoms in the atom tree. -/
abbrev PreVCondsTree := Tree PreVConds Unit

/-- This is different from `PreVCond` and instead holds proofs of variable conditions. Still, it
could either be a variable corresponding to a constraint, or an expression involving several
constraints, in case it is inferred. -/
abbrev VCond := Expr

/-- Several proofs of vconditions. -/
abbrev VConds := Array VCond

/-- All the vcondition proofs for the atom. -/
abbrev VCondsTree := Tree VConds Unit

/-- It is useful to only consider the vconditions that need to be eliminated because they match a
constraint exactly. This represents the index of such constraint. -/
abbrev VCondIdx := Nat

/-- Several `VCondIdx`s. -/
abbrev VCondsIdxs := Array VCondIdx

/-- All the indices of all the vconditions marked for elimination. -/
abbrev VCondsIdxsTree := Tree VCondsIdxs Unit


/- Solutions. -/

/-- A solution is just an expression (involving the atom arguments). -/
abbrev NewVarAssignment := Expr

/-- If an atom has several implementation variables, we need a solution for each of them. -/
abbrev Solution := Array NewVarAssignment


/- Canonized expressions. -/

/-- A canonized expression. -/
abbrev CanonExpr := Expr

/-- A tree of canonized expressions. -/
abbrev CanonExprsTree := Tree CanonExpr CanonExpr

/-- Canonized expression and solution put together.-/
structure CanonExprWithSolution where
  canonExpr : CanonExpr
  solution : Solution
deriving Inhabited

/-- Tree of canonized expression and solution for each atom. -/
abbrev CanonExprsWithSolutionTree := Tree CanonExprWithSolution CanonExprWithSolution


/- Proofs of solution equals atom expression. -/

/-- A proof of solution-equals-atom for an atom.-/
abbrev SolEqAtomProof := Expr

/-- Tree of all the solution-equals-atom proofs in the atom tree. -/
abbrev SolEqAtomProofsTree := Tree SolEqAtomProof SolEqAtomProof


/- Proofs of feasibility. -/

/-- A feasibility proof. -/
abbrev FeasibilityProof := Expr

/-- An atom may have several feasibility proofs, one per implementation constraint. -/
abbrev FeasibilityProofs := Array FeasibilityProof

/-- Tree of all the feasibility proofs in the atom tree. -/
abbrev FeasibilityProofsTree := Tree FeasibilityProofs Unit


/- Proofs of optimality and variable condition elimination. -/

/-- Optimality proof. There is only one per atom. -/
abbrev OptimalityProof := Expr

/-- Tree of all the optimality proofs in the atom tree. -/
abbrev OptimalityProofsTree := Tree OptimalityProof OptimalityProof

/-- A proof of vcondtion elimination. -/
abbrev VCondElimProof := Expr

/-- An atom may have several vconditions. Each needs a vcondition elimination proof. -/
abbrev VCondElimProofs := Array VCondElimProof

/-- Optimality and vcondition elimination proofs together. -/
abbrev OptimalityAndVCondElimProofs := OptimalityProof × VCondElimProofs

/-- Tree of all the optimality and vcondition elimination proofs in the atom tree. -/
abbrev OptimalityAndVCondElimProofsTree :=
  Tree OptimalityAndVCondElimProofs OptimalityAndVCondElimProofs

/-- Vcondition elimination map, from constraint index to the constraint expression. -/
abbrev VCondElimMap := Std.HashMap Nat Expr


/- Processed atom tree. -/

/-- This structure holds all the necessary information to build a canonized problem and a proof of
equivalence. In `CvxLean/Tactic/DCP/DCPMakers.lean`, we define the procedure that takes an
optimization problem, builds an atom tree and "processes" it to make a processed atom tree. -/
structure ProcessedAtomTree where
  originalVarsDecls : Array LocalDecl
  originalConstrVars : Array LocalDecl
  newVarDecls : List LocalDecl
  newConstrs : Array Expr
  newConstrVarsArray : Array LocalDecl
  forwardImagesNewVars : Array Expr
  constraints : List (Name × Expr)
  isVCond : Array Bool
  vcondElimMap : VCondElimMap
  solEqAtom : OC SolEqAtomProofsTree
  feasibility : OC FeasibilityProofsTree
  canonExprs : OC CanonExprsTree
  optimality : OC OptimalityProofsTree
deriving Inhabited

end DCP

end CvxLean
