import CvxLean.Syntax.Minimization
import CvxLean.Syntax.Prod
import CvxLean.Tactic.DCP.AtomLibrary.All
import CvxLean.Tactic.Basic.Rename
import CvxLean.Tactic.Basic.RenameConstr
import CvxLean.Tactic.Basic.RemoveConstr

open CvxLean
open Minimization
open Real

set_option trace.Meta.debug true
noncomputable def testVCondInference : Solution <|
  optimization (x : ℝ)
    minimize (x)
    subject to
      h1 : 0.001 ≤ x
      h2 : 1 ≤ sqrt x := by
  dcp
  sorry

-- noncomputable def test004 : Solution $
--   optimization (v w : ℝ)
--     minimize exp v
--     subject to
--       cv : 0 ≤ v
--       cw : 0 ≤ w
--       c0 :kl_div v w ≤ 1
-- := by
--   dcp
--   sorry

-- #print test004

set_option trace.Meta.debug true
noncomputable def test000 : Solution $
  optimization (x : Fin 3 → ℝ) (y : ℝ)
    minimize y
    subject to
      c0 : exp (Vec.sum (Vec.exp x)) ≤ y
:= by
  dcp
  sorry

-- TODO: This worked, but there are issues with the new multiplication atoms.
-- noncomputable def test001' (h : 0 ≤ (2 : ℝ)) (h : 0 ≤ (3 : ℝ)) : Solution $
--   optimization (x y : ℝ)
--     minimize y * (2 : ℝ)
--     subject to
--       c1 : (exp x) * (exp y) ≤ 3 * x
-- := by
--   dcp
--   sorry

-- ObjFun:(node:_uniq.7821 * 2[leaf:_uniq.7821, leaf:2])
--     Constr:
--     [
--      (node:Real.exp _uniq.7820 * Real.exp _uniq.7821 ≤ 3 * _uniq.7820
    --     [
    --       (node:Real.exp _uniq.7820 * Real.exp _uniq.7821
    --         [
    --           (node:Real.exp _uniq.7820[leaf:_uniq.7820]),
    --           (node:Real.exp _uniq.7821[leaf:_uniq.7821])
    --         ]
    --       ),
    --       (node:3 * _uniq.7820[leaf:3, leaf:_uniq.7820])
    --     ]
    --   )
    -- ]

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

-- noncomputable def test002 : Solution $
--   optimization (x y : ℝ)
--     minimize exp (huber y)
--     subject to
--       c0 : exp (exp (huber x)) ≤ y
-- := by
--   dcp
--   sorry

-- noncomputable def test003 (h : (0 : ℝ) ≤ 2): Solution $
--   optimization (x y : ℝ)
--     minimize (2 : ℝ) * (huber (y + x))
--     subject to
--       c0 : x ≤ y
-- := by
--   dcp
--   sorry

-- noncomputable def testVec0 [Fintype m] : Solution $
--   optimization (x y : m → ℝ)
--     minimize (0 : ℝ)
--     subject to
--       c0 : Vec.exp y ≤ x
-- := by
--   dcp
--   sorry

-- noncomputable def testVec [Fintype m] : Solution $
--   optimization (x y : m → ℝ)
--     minimize (0 : ℝ)
--     subject to
--       c0 : Vec.exp (Vec.exp x) ≤ x
-- := by
--   dcp
  -- sorry

-- noncomputable def test_Vec_huber [Fintype m] : Solution $
-- optimization (x y : m → ℝ)
--   minimize (0 : ℝ)
--   subject to
--     c0 : Vec.huber x ≤ x
-- := by
--   dcp
--   sorry

set_option trace.Meta.debug true

-- noncomputable def test_Vec_kl_div [Fintype m] : Solution $
-- optimization (x y : m → ℝ)
--   minimize (0 : ℝ)
--   subject to
--     cx : 0 < x
--     cy : 0 < y
--     c0 : Vec.kl_div x y ≤ x
-- := by
--   dcp
--   sorry

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



-- Example from Grant's thesis

-- noncomputable example (a : ℝ) (h : 0 ≤ a) : Solution $
--   minimization! (x y : ℝ) :
--     objective (c * x)
--     constraints
--       (cmain : exp y ≤ log (a * sqrt x + b))
--       (clin  : a * x + b * y = d)
--       (csqrt : 0 ≤ x)
--       (clog  : 0 < a * sqrt x + b)
-- := by
--   dcp
--   sorry




noncomputable def a1 : ℝ := 3
noncomputable def b1 : ℝ := 4
noncomputable def c1 : ℝ := 5
noncomputable def d1 : ℝ := 6

set_option trace.Elab.debug true

-- TODO:
-- noncomputable example : Solution $
--   minimization! (x y : ℝ) :
--     objective (x)
--     constraints
--       (hlog : 0 < exp a1)
--       (e : exp y ≤ log (exp a1))
--       (hsqrt : 0 ≤ x) := by
--   dcp
