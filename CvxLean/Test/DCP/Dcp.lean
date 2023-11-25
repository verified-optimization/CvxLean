import CvxLean.Syntax.Minimization
import CvxLean.Syntax.Prod
import CvxLean.Tactic.DCP.AtomLibrary.All
import CvxLean.Tactic.Basic.Rename
import CvxLean.Tactic.Basic.RenameConstr
import CvxLean.Tactic.Basic.RemoveConstr

open CvxLean Minimization Real

noncomputable def testVCondInference : Solution <|
  optimization (x : ℝ)
    minimize (x)
    subject to
      h1 : 0.001 ≤ x
      h2 : 1 ≤ sqrt x := by
  dcp
  sorry

set_option trace.Meta.debug true
noncomputable def test004 : Solution $
  optimization (v w : ℝ)
    minimize exp v
    subject to
      cv : 0 ≤ v
      cw : 0 < w
      c0 : klDiv v w ≤ 1
:= by
  dcp
  sorry

set_option trace.Meta.debug true
noncomputable def test000 : Solution $
  optimization (x : Fin 3 → ℝ) (y : ℝ)
    minimize y
    subject to
      c0 : exp (Vec.sum (Vec.exp x)) ≤ y
:= by
  dcp
  sorry

noncomputable def test001'' (h : 0 ≤ (2 : ℝ)) (h : 0 ≤ (3 : ℝ)) : Solution $
  optimization (x y : ℝ)
    minimize y * (2 : ℝ)
    subject to
      c1 : exp (exp x) ≤ 3 * x
:= by
  dcp
  sorry

noncomputable def test001 : Solution $
  optimization (x y : ℝ)
    minimize exp $ exp (abs x)
    subject to
      c0 : exp (abs x) ≤ 0
      c' : 0 < y
      c1 : exp (exp (exp (exp (exp x)))) ≤ log y
:= by
  dcp
  sorry

noncomputable def test002 : Solution $
  optimization (x y : ℝ)
    minimize exp (huber y)
    subject to
      c0 : exp (exp (huber x)) ≤ y
:= by
  dcp
  sorry

noncomputable def test003 : Solution $
  optimization (x y : ℝ)
    minimize (2 : ℝ) * (huber (y + x))
    subject to
      c0 : x ≤ y
:= by
  dcp
  sorry

-- TODO: any fin type
noncomputable def testVec0 : Solution $
  optimization (x y : Fin m → ℝ)
    minimize (0 : ℝ)
    subject to
      c0 : Vec.exp y ≤ x
:= by
  dcp
  sorry

-- TODO: any fin type
noncomputable def testVec : Solution $
  optimization (x y : Fin m → ℝ)
    minimize (0 : ℝ)
    subject to
      c0 : Vec.exp (Vec.exp x) ≤ x
:= by
  dcp
  sorry

noncomputable def test_Vec_huber {n : ℕ} : Solution $
optimization (x y : Fin n → ℝ)
  minimize (0 : ℝ)
  subject to
    c0 : Vec.huber x ≤ x
:= by
  dcp
  sorry

-- TODO: notation.
-- TODO: error if the constraint is ∀ i
noncomputable def test_Vec_kl_div {n : ℕ} : Solution $
optimization (x y : Fin n → ℝ)
  minimize (0 : ℝ)
  subject to
    cx : 0 ≤ x
    cy : StrongLT 0 y
    -- cy : ∀ i, 0 < (y) i
    c0 : Vec.klDiv x y ≤ x
:= by
  dcp
  sorry

noncomputable def test2 : Solution $
  optimization (x y : ℝ)
    minimize x
    subject to
      c0 : 0 < x
      c1 : 0 < log x
      c2 : 0 ≤ log (log x)
:= by
  dcp
  sorry

noncomputable def test_log_det : Solution $
  optimization (M : Matrix (Fin n) (Fin n) ℝ)
    minimize (0 : ℝ)
    subject to
      c0 : 0 ≤ Real.log M.det
      c_pos_def : M.PosDef
:= by
  dcp
  sorry


noncomputable example
  (a : ℝ) (ha : 0 ≤ a)
  (b : ℝ) (hb : 0 ≤ b)
  (c : ℝ) (hc : 0 ≤ c) : Solution $
  optimization (x y : ℝ)
    minimize (c * x)
    subject to
      cmain : exp y ≤ log (a * sqrt x + b)
      clin  : a * x + b * y = d
      csqrt : 0 ≤ x
      clog  : 0 < a * sqrt x + b
:= by
  dcp
  sorry


noncomputable def a1 : ℝ := 3
noncomputable def b1 : ℝ := 4
noncomputable def c1 : ℝ := 5
noncomputable def d1 : ℝ := 6

set_option trace.Elab.debug true

-- TODO:
noncomputable example : Solution $
  optimization (x y : ℝ)
    minimize (x)
    subject to
      hlog : 0 ≤ exp a1
      e : exp y ≤ log (exp a1)
      hsqrt : 0 ≤ x := by
  dcp -- TODO: first constraint not reduced. We need to handle constant constraints.
  sorry
