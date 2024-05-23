import CvxLean.Command.Solve.Solvers.ECOS.SparseMatrix

/-!
Representation of an input problem for the ECOS solver.
-/

namespace ECOS

/-- Encoding of an optimisation problem of the form:
```
    minimize      cᵀx
    subject to   Ax = b
                Gx ≤K h
```-/
structure Problem (α : Type) :=
  -- Number of primal variables.
  (n : Int)
  -- Number of constraints (length of h).
  (m : Int)
  -- Number of equality constraints (length of b).
  (p : Int)
  -- Dimension of the positive orthant ℝˡ₊.
  (l : Int)
  --  Number of second-order cones present in problem.
  (ncones : Int)
  -- Array of length ncones; q[i] defines the dimension of the cone i.
  (q : Array Int)
  -- Number of exponential cones present in problem.
  (e : Int)
  -- Matrix G.
  (G : SparseMatrix α)
  -- Matrix A.
  (A : SparseMatrix α)
  -- Vector c.
  (c : Array α)
  -- Vector h.
  (h : Array α)
  -- Vector b.
  (b : Array α)

end ECOS
