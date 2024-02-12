import CvxLean.Tactic.DCP.AtomLibrary.All

noncomputable section Basic

open CvxLean Minimization Real

section Atoms

def testKLDiv : Solution <|
    optimization (v w : ℝ)
      minimize exp v
      subject to
        c1 : 0 ≤ v
        c2 : 1 / 100000 ≤ w
        c3 : klDiv v w ≤ 1 := by
  dcp
  sorry

def testXExp : Solution <|
    optimization (x : ℝ)
      minimize x * exp x
      subject to
        c1 : 0 ≤ x := by
  dcp
  sorry

def testEntr : Solution <|
    optimization (x : ℝ)
      minimize -(-(x * log x))
      subject to
        c1 : 0 ≤ x := by
  dcp
  sorry

def testQuadOverLin : Solution <|
    optimization (x y : ℝ)
      minimize x ^ (2 : ℝ) / y
      subject to
        c1 : 0 ≤ x
        c2 : 1 / 100000 ≤ y := by
  dcp
  sorry

def testGeoMean : Solution <|
    optimization (x y : ℝ)
      minimize - (sqrt (x * y))
      subject to
        c1 : 0 ≤ x
        c2 : 0 ≤ y := by
  dcp
  sorry

def testNorm2 : Solution <|
    optimization (x y : ℝ)
      minimize ‖![x, y]‖
      subject to
        c1 : 0 ≤ x
        c2 : 0 ≤ y := by
  dcp
  sorry

variable {m}

def testVecExp : Solution <|
    optimization (x y : Fin m → ℝ)
      minimize (0 : ℝ)
      subject to
        c1 : Vec.exp y ≤ x := by
  dcp
  sorry

def testVecExp2 : Solution <|
    optimization (x y : Fin m → ℝ)
      minimize (0 : ℝ)
      subject to
        c1 : Vec.exp (Vec.exp x) ≤ x := by
  dcp
  sorry

def testVecHuber {n : ℕ} : Solution <|
    optimization (x y : Fin n → ℝ)
      minimize (0 : ℝ)
      subject to
        c0 : Vec.huber x ≤ x := by
  dcp
  sorry

def testVecKLDiv {n : ℕ} : Solution <|
    optimization (x y : Fin n → ℝ)
      minimize (0 : ℝ)
      subject to
        c1 : 0 ≤ x
        c2 : 1 / 100000 ≤ y
        c3 : Vec.klDiv x y ≤ x := by
  dcp
  sorry

def testLog : Solution <|
    optimization (x y : ℝ)
      minimize x
      subject to
        c1 : 0 < x
        c2 : 0 < log x
        c3 : 0 ≤ log (log x) := by
  dcp
  sorry

def testLogDet {n : ℕ} : Solution <|
    optimization (M : Matrix (Fin n) (Fin n) ℝ)
      minimize (0 : ℝ)
      subject to
        c1 : 0 ≤ Real.log M.det
        c2 : M.PosDef := by
  dcp
  sorry

open BigOperators in
def testBinders {n} : Solution <|
    optimization (x : Fin n → ℝ)
      minimize ∑ i, x i
      subject to
        c1 : ∀ i, 1 ≤ x i := by
  dcp
  sorry

end Atoms

section Misc

variable {d : ℝ}

def testGrantsThesis (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : Solution <|
    optimization (x y : ℝ)
      minimize (c * x)
      subject to
        c1 : exp y ≤ log (a * sqrt x + b)
        c2 : a * x + b * y = d
        c3 : 0 ≤ x
        c4 : 0 < a * sqrt x + b := by
  dcp
  sorry

def a1 : ℝ := 3
def b1 : ℝ := 4
def c1 : ℝ := 5
def d1 : ℝ := 6

def testWithConstants : Solution <|
  optimization (x y : ℝ)
    minimize (x)
    subject to
      c1 : 0 ≤ exp a1
      c2 : exp y ≤ log (exp a1)
      c3 : 0 ≤ x := by
  dcp
  sorry

def testVCondInference : Solution <|
    optimization (x : ℝ)
      minimize (x)
      subject to
        c1 : 0.001 ≤ x
        c2 : 1 ≤ sqrt x := by
  dcp
  sorry

def testVecSumAndExp : Solution <|
    optimization (x : Fin 3 → ℝ) (y : ℝ)
      minimize y
      subject to
        c1 : exp (Vec.sum (Vec.exp x)) ≤ y := by
  dcp
  sorry

def testExp : Solution <|
    optimization (x y : ℝ)
      minimize y * (2 : ℝ)
      subject to
        c1 : exp (exp x) ≤ 3 * x := by
  dcp
  sorry

def testDeepComposition : Solution <|
    optimization (x y : ℝ)
      minimize exp (exp (abs x))
      subject to
        c1 : exp (abs x) ≤ 0
        c2 : 0 < y
        c3 : exp (exp (exp (exp (exp x)))) ≤ log y := by
  dcp
  sorry

def testHuber2 : Solution <|
    optimization (x y : ℝ)
      minimize exp (huber y)
      subject to
        c2 : exp (exp (huber x)) ≤ y := by
  dcp
  sorry

def testHuber3 : Solution <|
    optimization (x y : ℝ)
      minimize 2 * (huber (y + x))
      subject to
        c1 : x ≤ y := by
  dcp
  sorry

end Misc

end Basic
