import CvxLean.Lib.Minimization
import CvxLean.Tactic.Solver.Float.RealToFloat
import CvxLean.Tactic.Solver.Float.OptimizationParam

section RealToFloat

-- Simple tests.

#realToFloat Real

#realToFloat (8 : Real)

#realToFloat (0 : Real) + 1

#realToFloat Real.exp 1

#realToFloat fun (p : Real × (Fin 2 → Real)) => Real.exp p.1 + p.2 1 ≤ 0 ∧ Real.exp p.1 + p.2 1 ≤ 0

#realToFloat (1 : Real) = 3

-- Convert whole minimization problem.

#realToFloat @Minimization.mk Real Real (fun (x : Real) => x) (fun (x : Real) => x <= 0)

-- Test optimizationParam.

@[optimizationParam]
noncomputable def A : ℝ := 1

#realToFloat A

noncomputable def B : ℝ := 1

#realToFloat B

end RealToFloat
