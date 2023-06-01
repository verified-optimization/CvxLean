import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify

noncomputable section GP

open CvxLean Minimization Real

section Basic

lemma test : Solution (
    optimization (x : ℝ)
      minimize (x)
      subject to
        hx : 0 < x
        h : x ^ 2 ≤ -10.123
) := by
  map_exp
  convexify
  sorry

lemma test2 : Solution (
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x 
      h5 : x <= 3
      h6 : x^2 <= sqrt x - 6 * y / z
      h7 : x * y = z) := by 
  map_exp
  convexify
  sorry

end Basic

section GPTutorialPaper

-- https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (4)

-- NOTE(RFM): `maximize` does not work because it is set to `Neg.neg`.
def gp1 :=
  optimization (x y z : ℝ) 
    minimize 1 / (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x
      h5 : x <= 3 
      h6 : x^2 + 3 * y / z <= sqrt x
      h7 : x / y = z^2

set_option trace.Meta.debug true

reduction red/dcp1 : gp1 := by 
  map_exp
  convexify
  exact done

#print dcp1
-- def dcp1 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize y - x
--   subject to
--     _ : log 2 ≤ x
--     _ : exp x ≤ 3
--     _ : exp (x * (3 / 2)) + 3 * exp (y + (-(x * (1 / 2)) - z)) ≤ 1
--     _ : x - y = 2 * z

-- https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (5)

@[optimizationParam]
def Awall : ℝ := 10

@[optimizationParam]
def Aflr : ℝ := 10

@[optimizationParam]
def α : ℝ := 3

@[simp]
lemma α_pos : 0 < α := by unfold α; norm_num

@[optimizationParam]
def β : ℝ := 4

@[simp]
lemma β_pos : 0 < β := by unfold β; norm_num

@[optimizationParam]
def γ : ℝ := 5

@[simp]
lemma γ_pos : 0 < γ := by unfold γ; norm_num

@[optimizationParam]
def δ : ℝ := 6

@[simp]
lemma δ_pos : 0 < δ := by unfold δ; norm_num

def gp2 :=
  optimization (h w d : ℝ) 
    minimize (1 / h) * (1 / w) * (1 / d)
    subject to 
      h1 : 0 < h
      h2 : 0 < w
      h3 : 0 < d
      h4 : 2 * (h * d + w * d) ≤ Awall
      h5 : w * d ≤ Aflr
      h6 : α ≤ h/w
      h7 : h/w ≤ β  
      h8 : γ ≤ d/w
      h9 : d/w ≤ δ

reduction red2/dcp2 : gp2 := by
  map_exp
  convexify
  exact done

#print dcp2
-- def dcp2 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (h : ℝ) (w : ℝ) (d : ℝ) 
--   minimize -h + (-w - d)
--   subject to
--     _ : 2 * exp (d + h) + 2 * exp (w + d) ≤ Awall
--     _ : exp (w + d) ≤ Aflr
--     _ : log α ≤ h - w
--     _ : exp (h - w) ≤ β
--     _ : log γ ≤ d - w
--     _ : d ≤ log δ + w

-- https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf 2.1

-- NOTE(RFM): We don't have the power atom yet.
def gp3 := 
  optimization ( x y z : ℝ) 
    --minimize (x ^ (-1)) * y ^ (-1 / 2) * z ^ (-1) + 2.3 * x * z + 4 * x * y * z
    minimize (1 / x) * (1 / sqrt y) * (1 / z) + (2.3) * x * z + 4 * x * y * z
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      --h4 : (1 / 3) * x ^ (-2) * y ^ (-2) + (4 / 3) * y ^ (1 / 2) * z ^ (-1) ≤ 1
      h4 : (1 / 3) * (1 / (x ^ 2)) * (1 / (y ^ 2)) + (4 / 3) * (sqrt y) * (1 / z) ≤ 1
      h5 : x + 2 * y + 3 * z ≤ 1
      h6 : (1 / 2) * x * y = 1

set_option maxHeartbeats 1000000
reduction red3/dcp3 : gp3 := by
  map_exp
  convexify
  exact done

#print dcp3
-- def dcp3 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize exp (-(y * (1 / 2)) - x - z) + (23 * (exp (z + x) / 10) + 4 * exp (y + (z + x)))
--   subject to
--     _ : 1 / 3 * exp (-(y * 2) + -(2 * x)) + 1 / 3 * (4 * exp (y * (1 / 2) - z)) ≤ 1
--     _ : exp x + (exp y * 2 + exp z * 3) ≤ 1
--     _ : y + (x - log 2) = 0

end GPTutorialPaper

section QuasiConvex

def qp1 := 
  optimization (x y : ℝ) 
    minimize - (sqrt x) / y
    subject to 
      h1 : 0 < y
      h2 : (exp x) ≤ y

reduction redq1/dcpq1 : qp1 := by
  unfold qp1
  -- convexify
  exact done

end QuasiConvex

end GP
