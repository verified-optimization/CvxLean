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

abbrev Argument := Expr
abbrev Arguments := Array Argument

/-- -/
abbrev ArgumentsTree := Tree Arguments Unit


/- Curvature. -/

abbrev CurvatureTree := Tree Curvature Curvature


/- Background conditions. -/

abbrev BCond := Expr
abbrev BConds := Array BCond
abbrev BCondsTree := Tree BConds BConds


/- Result of finding an atom. -/

/-- Four trees: atom data tree, arguments tree, curvature tree, and background condition tree. -/
abbrev AtomDataTrees := GraphAtomDataTree × ArgumentsTree × CurvatureTree × BCondsTree


/-- New variables and constraints. -/

abbrev NewVarsTree := Tree (Array LocalDecl) Unit

abbrev NewConstrVarsTree := Tree (Array LocalDecl) Unit


/- New constraints (expressions). -/

abbrev NewConstrsTree := Tree (Array Expr) Unit


/- Variable condtions. -/

abbrev PreVCond := Nat ⊕ Expr
abbrev PreVConds := Array PreVCond
abbrev PreVCondsTree := Tree PreVConds Unit

abbrev VCond := Expr
abbrev VConds := Array VCond
abbrev VCondsTree := Tree VConds Unit

abbrev VCondIdx := Nat
abbrev VCondsIdxs := Array VCondIdx
abbrev VCondsIdxsTree := Tree VCondsIdxs Unit


/- Solutions. -/

-- One variable
/-- -/
abbrev NewVarAssignment := Expr

abbrev Solution := Array NewVarAssignment


/- Canonized expressions. -/

abbrev CanonExpr := Expr
abbrev CanonExprsTree := Tree CanonExpr CanonExpr

structure CanonExprWithSolution where
  canonExpr : CanonExpr
  solution : Solution

instance : Inhabited CanonExprWithSolution := ⟨⟨default, default⟩⟩

abbrev CanonExprsWithSolutionTree := Tree CanonExprWithSolution CanonExprWithSolution

/- Proofs of solution equals atom expression. -/

abbrev SolEqAtomProof := Expr
abbrev SolEqAtomProofsTree := Tree SolEqAtomProof SolEqAtomProof


/- Proofs of feasibility. -/

abbrev FeasibilityProof := Expr
abbrev FeasibilityProofs := Array FeasibilityProof
abbrev FeasibilityProofsTree := Tree FeasibilityProofs Unit


/- Proofs of optimality and variable condition elimination. -/

abbrev OptimalityProof := Expr
abbrev OptimalityProofsTree := Tree OptimalityProof OptimalityProof

abbrev VCondElimProof := Expr
abbrev VCondElimProofs := Array VCondElimProof

abbrev OptimalityAndVCondElimProofs := OptimalityProof × VCondElimProofs
abbrev OptimalityAndVCondElimProofsTree :=
  Tree OptimalityAndVCondElimProofs OptimalityAndVCondElimProofs

abbrev VCondElimMap := Std.HashMap Nat Expr


/- Processed atom tree. -/

/-- -/
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

instance : Inhabited ProcessedAtomTree :=
  ⟨⟨#[], #[], [], #[], #[], #[], [], #[], {}, default, default, default, default⟩⟩

end DCP

end CvxLean
