import CvxLean.Lib.Minimization
import CvxLean.Syntax.OptimizationParam
import CvxLean.Command.Solve.Float.RealToFloatLibrary

/-!
Real-to-float tests.
-/

section RealToFloat

-- Simple tests.

#real_to_float Real

#real_to_float (8 : Real)

#real_to_float (0 : Real) + 1

#real_to_float Real.exp 1

#real_to_float fun (p : Real × (Fin 2 → Real)) =>
  Real.exp p.1 + p.2 1 ≤ 0 ∧ Real.exp p.1 + p.2 1 ≤ 0

#real_to_float (1 : Real) = 3

#real_to_float (2 • (1 : Matrix (Fin 1) (Fin 1) Real))

-- Convert whole minimization problem.

#real_to_float @Minimization.mk Real Real (fun (x : Real) => x) (fun (x : Real) => x <= 0)

-- Test optimization_param.

@[optimization_param]
noncomputable def A : ℝ := 1

#real_to_float A

noncomputable def B : ℝ := 1

#real_to_float B

end RealToFloat
