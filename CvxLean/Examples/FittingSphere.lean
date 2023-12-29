import CvxLean.Lib.Equivalence
import CvxLean.Command.Solve

open CvxLean Minimization
open Matrix Real BigOperators

namespace FittingSphere

noncomputable section

variable {n : ℕ} {m : ℕ} (x : Fin m → Fin n → ℝ)

def p :=
  optimization (c : Fin n → ℝ) (r : ℝ)
    minimize ((∑ i, (‖x i - c‖ ^ 2 - r ^ 2)) ^ 2 : ℝ)
    subject to
      h1 : 0 ≤ c
      h2 : 0 ≤ r

reduction ψ/q {n m : ℕ} (x : Fin m → Fin n → ℝ) : p x := by
  unfold p
  -- dcp -- fails because of ∑

end

end FittingSphere
