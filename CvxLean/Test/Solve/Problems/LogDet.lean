import CvxLean.Command.Solve

/-!
Testing the log-det atom.
-/

section LogDet

open CvxLean Minimization Real

noncomputable def logDet1 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    minimize (Matrix.trace X)
    subject to
      c1 : 10 ≤ log X.det
      c2 : X.PosDef

solve logDet1

#eval logDet1.status       -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval logDet1.value        -- 296.826317
#eval logDet1.solution 0 0 -- 148.413156
#eval logDet1.solution 0 1 -- 0.000000
#eval logDet1.solution 1 0 -- 0.000000
#eval logDet1.solution 1 1 -- 148.413156

noncomputable def logDet2 :=
  optimization (X : Matrix (Fin 2) (Fin 2) ℝ)
    maximize (log X.det)
    subject to
      c1 : X.PosDef
      c2 : X 0 0 + X 0 1 + X 1 1 ≤ 50

solve logDet2

#print logDet2.conicForm

#eval logDet2.status       -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval logDet2.value        -- 6.725434
#eval logDet2.solution 0 0 -- 33.336064
#eval logDet2.solution 0 1 -- -16.665855
#eval logDet2.solution 1 0 -- -16.665855
#eval logDet2.solution 1 1 -- 33.329791

end LogDet
