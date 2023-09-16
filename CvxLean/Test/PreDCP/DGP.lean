import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Test.Util.TimeCmd

noncomputable section GP

open CvxLean Minimization Real

section GP1

def gp1 :=
    optimization (x : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : x ^ 2 ≤ 10.123

time_cmd reduction red1/dcp1 : gp1 := by
  map_exp
  convexify

#print dcp1
-- def dcp1 : Minimization ℝ ℝ :=
-- optimization (x : ℝ) 
--   minimize x
--   subject to
--     h2 : x * 2 ≤ log (10123 / 1000)

solve dcp1

end GP1

section GP2

def gp2 :=
    optimization (x y : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : 0 < y
        h3 : x * y ≤ 5.382

time_cmd reduction red2/dcp2 : gp2 := by
  map_exp
  convexify

#print dcp2
-- def dcp2 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) 
--   minimize x
--   subject to
--     h3 : x ≤ log (2691 / 500) - y

solve dcp2

end GP2

section GP3 

def gp3 :=
    optimization (x y : ℝ)
      minimize (x)
      subject to
        h1 : 0 < x
        h2 : 0 < y
        h3 : sqrt (x * x + y) ≤ 1

time_cmd reduction red3/dcp3 : gp3 := by
  map_exp
  convexify

#print dcp3
-- def dcp3 : Minimization (ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) 
--   minimize x
--   subject to
--     h3 : exp (x * 2) + exp y ≤ 1

solve dcp3

end GP3

section GP4 

def gp4 := 
  optimization (x y z : ℝ) 
    minimize (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 <= x 
      h5 : x <= 3
      h6 : x ^ 2 + 6 * y / z <= sqrt x
      h7 : x * y = z

time_cmd reduction red4/dcp4 : gp4 := by
  map_exp
  convexify

solve dcp4

#print dcp4
-- def dcp4 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize x - y
--   subject to
--     h4 : log 2 ≤ x
--     h5 : x ≤ log 3
--     h6 : exp (x * (3 / 2)) + 6 * exp (y - z - x * (1 / 2)) ≤ 1
--     h7 : x + y = z

end GP4

/- https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (4). -/
section GP5

-- NOTE: `maximize` does not work because it is set to `Neg.neg`.
def gp5 :=
  optimization (x y z : ℝ) 
    minimize 1 / (x / y)
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 ≤ x
      h5 : x ≤ 3 
      h6 : x^2 + 3 * y / z ≤ sqrt x
      h7 : x / y = z ^ 2

time_cmd reduction red5/dcp5 : gp5 := by 
  map_exp
  convexify

#print dcp5
-- def dcp5 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize -(x - y)
--   subject to
--     h4 : log 2 ≤ x
--     h5 : x ≤ log 3
--     h6 : exp (x * (3 / 2)) + 3 * exp (y - z - x * (1 / 2)) ≤ 1
--     h7 : x - y = 2 * z

solve dcp5

end GP5

-- TODO: Issue with repeated rewrites.
-- /- In https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf (5) and in
-- https://www.cvxpy.org/examples/dgp/max_volume_box.html -/
-- section GP6

-- -- NOTE: `maximize` issue.
-- def gp6 :=
--   optimization (h w d : ℝ) 
--     minimize (1 / (h * w * d))
--     subject to 
--       h1 : 0 < h
--       h2 : 0 < w
--       h3 : 0 < d
--       h4 : 2 * (h * d + w * d) ≤ 100
--       h5 : w * d ≤ 10
--       h6 : 0.5 ≤ h / w
--       h7 : h / w ≤ 0.5  
--       h8 : 5 ≤ d / w
--       h9 : d / w ≤ 6

-- time_cmd reduction red6/dcp6 : gp6 := by
--   map_exp
--   convexify

-- #print dcp6
-- -- def dcp6 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- -- optimization (h : ℝ) (w : ℝ) (d : ℝ) 
-- --   minimize -(h + (d + w))
-- --   subject to
-- --     h4 : 2 * (exp (h + d) + exp (d + w)) ≤ 100
-- --     h5 : d + w ≤ log 10
-- --     h6 : w - log 2 ≤ h
-- --     h7 : h ≤ w - log 2
-- --     h8 : log 5 ≤ d - w
-- --     h9 : d - w ≤ log 6

-- solve dcp6

-- end GP6

/- In https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf section 2.2. -/
section GP7

-- NOTE: We don't have the power atom yet.
-- objFun : (x ^ (-1)) * y ^ (-1 / 2) * z ^ (-1) + 2.3 * x * z + 4 * x * y * z
-- h4 : (1 / 3) * x ^ (-2) * y ^ (-2) + (4 / 3) * y ^ (1 / 2) * z ^ (-1) ≤ 1
def gp7 := 
  optimization (x y z : ℝ) 
    minimize (1 / x) * (1 / sqrt y) * (1 / z) + (2.3) * x * z + 4 * x * y * z
    subject to 
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : (1 / 3) * (1 / (x ^ 2)) * (1 / (y ^ 2)) + (4 / 3) * (sqrt y) * (1 / z) ≤ 1
      h5 : x + 2 * y + 3 * z ≤ 1
      h6 : (1 / 2) * x * y = 1

set_option maxHeartbeats 1000000
time_cmd reduction red7/dcp7 : gp7 := by
  map_exp
  convexify

#print dcp7
-- def dcp7 : Minimization (ℝ × ℝ × ℝ) ℝ :=
-- optimization (x : ℝ) (y : ℝ) (z : ℝ) 
--   minimize exp (y * -(1 / 2) - z - x) + (23 / 10 * exp (x + z) + 4 * exp (x + (y + z)))
--   subject to
--     h4 : exp (-2 * (x + y)) / 3 ≤ 1 - 4 / 3 * exp (y * (1 / 2) - z)
--     h5 : exp z * 3 ≤ 1 - exp x - exp y * 2
--     h6 : x + (y - log 2) = 0

solve dcp7

end GP7
