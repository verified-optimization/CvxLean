import Lean

/-!
# Curvature rules

This file contains the definition of the `Curvature` and `ArgKind` types, as well as the function
`curvatureInArg` that calculates the curvature of an atom depending on the monotonicity of its
arguments. This corresponds to the DCP composition rules. It is used in a crucial way to make atom
trees by the `dcp` tactic.
-/

namespace CvxLean

open Lean

/-- An atom can be affine, concave or convex. -/
inductive Curvature where
  | Constant | Affine | Concave | Convex | AffineSet | ConvexSet
deriving BEq, Inhabited

instance : ToMessageData Curvature where
  toMessageData
  | Curvature.Constant => "constant"
  | Curvature.Affine => "affine"
  | Curvature.Concave => "concave"
  | Curvature.Convex => "convex"
  | Curvature.AffineSet => "affine_set"
  | Curvature.ConvexSet => "convex_set"

/-- Arguments of an atom are increasing (+), decreasing (-), constant (&) or neither (?). -/
inductive ArgKind where
  | Increasing | Decreasing | Neither | Constant
deriving BEq, Inhabited

instance : ToMessageData ArgKind where
  toMessageData
  | ArgKind.Increasing => "increasing"
  | ArgKind.Decreasing => "decreasing"
  | ArgKind.Neither => "neither"
  | ArgKind.Constant => "constant"

/-- Given an expression of the form `f(e₁, ..., eₙ)`, where `f` corresponds to an atom with
curvature `c` and its `i`th argument has monotonicity (or, rather, `ArgKind`) `aᵢ`, this function
calculates the **expected** curvature of `eᵢ` from `c` and `aᵢ`. -/
def curvatureInArg : Curvature → ArgKind → Curvature
  | _, ArgKind.Constant => Curvature.Constant
  | Curvature.Concave, ArgKind.Increasing => Curvature.Concave
  | Curvature.Concave, ArgKind.Decreasing => Curvature.Convex
  | Curvature.Convex, ArgKind.Increasing => Curvature.Convex
  | Curvature.Convex, ArgKind.Decreasing => Curvature.Concave
  -- This requires some explanation. The only set atom that allows non-affine arguments is `≤`. The
  -- rest, equality and cones, require affine arguments. We say that an expression `x ≤ y` is
  -- decreasing in `x` in the following sense: if `x' ≤ x` then `x ≤ y → x' ≤ y`, where `→` is seen
  -- as the order relation in `Prop`.
  | Curvature.ConvexSet, ArgKind.Increasing => Curvature.Concave
  | Curvature.ConvexSet, ArgKind.Decreasing => Curvature.Convex
  | _, _ => Curvature.Affine

end CvxLean
