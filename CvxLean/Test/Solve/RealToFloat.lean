import CvxLean.Lib.Minimization
import CvxLean.Syntax.OptimizationParam
import CvxLean.Command.Solve.Float.RealToFloat

section RealToFloat

-- Simple tests.

#realToFloat Real

#realToFloat (8 : Real)

#realToFloat (0 : Real) + 1

#realToFloat Real.exp 1

#realToFloat fun (p : Real × (Fin 2 → Real)) => Real.exp p.1 + p.2 1 ≤ 0 ∧ Real.exp p.1 + p.2 1 ≤ 0

#realToFloat (1 : Real) = 3

#realToFloat (2 • (1 : Matrix (Fin 1) (Fin 1) Real))

-- Convert whole minimization problem.

#realToFloat Real.Matrix.PSDCone (2 • (1 : Matrix (Fin 1) (Fin 1) Real))

#realToFloat Real.Matrix.posOrthCone (1 : Matrix (Fin 1) (Fin 1) Real)

#realToFloat @Minimization.mk Real Real (fun (x : Real) => x) (fun (x : Real) => x <= 0)

-- Test optimization_param.

@[optimization_param]
noncomputable def A : ℝ := 1

#realToFloat A

noncomputable def B : ℝ := 1

#realToFloat B

end RealToFloat
