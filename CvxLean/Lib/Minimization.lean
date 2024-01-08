import Mathlib.Order.Bounds.Basic

/-!
# Minimization and Solution

This file defines:
* `Minimization`: the type of optimization problems, which we assume to be minimization problems.
* `Solution`: the type representing the solution set for an optimization problem.

These are the building blocks of the rest of the library.
-/

/-- Type of an optimization problem. -/
structure Minimization (D R : Type) where
  objFun : D → R
  constraints : D → Prop

namespace Minimization

/-- We assume constraints are joind by `∧`. A problem with several constraints can be written as
`⟨f, [[c1, ..., cn]]⟩`. -/
syntax (name := constrNotation) "[[" term,* "]]" : term

macro_rules
  | `([[]]) => `(fun x => True)
  | `([[$c:term]]) => `(fun x => $c x)
  | `([[$c:term, $cs:term,*]]) => `(fun x => $c x ∧ ([[$cs,*]] x))

variable {D E R : Type} [Preorder R]
variable (p : Minimization D R) (q : Minimization E R)

/-- A point `x : D` is feasible in `p` if it satisfies the constraints. -/
@[reducible]
def feasible (x : D) : Prop := p.constraints x

/-- A point `x : D` is optimal in `p` if it is feasible and for any feasible point `y : D` the
value of `x` is a lower bound to the value of `y`. -/
@[reducible]
def optimal (x : D) : Prop := p.feasible x ∧ ∀ y, p.feasible y → p.objFun x ≤ p.objFun y

/-- A solution is simply an optimal point. Note that the `optimality` property is only the second
half of `optimal`. -/
structure Solution where
  point : D
  feasibility : p.feasible point
  optimality : ∀ y, p.feasible y → p.objFun point ≤ p.objFun y

end Minimization
