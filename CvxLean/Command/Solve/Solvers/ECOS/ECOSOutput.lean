import CvxLean.Command.Solve.Solvers.ECOS.SparseMatrix

/-!
Representation of the output of the ECOS solver.
-/

namespace ECOS

structure Result (α : Type) :=
  -- Exit flag, `0` if optimal.
  (exitflag : Int)
  -- Optimal value.
  (cx : α)
  -- Optimal point.
  (x : Array α)

instance {α} [h : Inhabited α] : Inhabited (Result α) where
  default := { exitflag := 0, cx := h.default, x := #[] }

end ECOS
