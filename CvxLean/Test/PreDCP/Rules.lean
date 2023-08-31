import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Tactic.Conv.ConvOpt
import CvxLean.Test.Util.TimeCmd

noncomputable section Rules

open CvxLean Minimization Real


/- Equality rules. -/

-- log_eq_log
def logEqLogConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : exp x = exp x

time_cmd equivalence logEqLogConstrRedAuto/logEqLogConstrAuto : logEqLogConstr := by
  unfold logEqLogConstr
  convexify

#print logEqLogConstrAuto


/- Less than or equal rules. -/

-- le_sub_iff_add_le
def leSubIffAddLeConstr := 
  optimization (x y : ℝ)
    minimize (0 + 1 + 0 : ℝ)
    subject to
      h : x ≤ 1 - x

time_cmd equivalence leSubIffAddLeConstrRedAuto/leSubIffAddLeConstrAuto : leSubIffAddLeConstr := by 
  unfold leSubIffAddLeConstr
  convexify

#check leSubIffAddLeConstrRedAuto

-- div_le_iff
def divLeIffConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hy : 0 < y
      h : x / y ≤ 1
  
time_cmd equivalence divLeIffConstrRedAuto/divLeIffConstrAuto : divLeIffConstr := by
  unfold divLeIffConstr
  convexify

-- div_le_iff-rev 
def divLeIffRevConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hy : 0 < x
      h : x ≤ x * y

time_cmd equivalence divLeIffRevConstrRedAuto/divLeIffRevConstrAuto : divLeIffRevConstr := by
  unfold divLeIffRevConstr
  convexify

-- log_le_log
def logLeLogConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      hy : 0 < y
      h : log x ≤ log y

time_cmd equivalence logLeLogConstrRedAuto/logLeLogConstrAuto : logLeLogConstr := by
  unfold logLeLogConstr
  convexify

-- log_le_log-rev
def logLeLogRevConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : exp x ≤ exp y

time_cmd equivalence logLeLogRevConstrRedAuto/logLeLogRevConstrAuto : logLeLogRevConstr := by
  unfold logLeLogRevConstr
  convexify



/- Field rules -/

-- one_mul 

-- one_mul-rev 

-- add_comm

-- add_assoc

-- mul_comm

-- mul_assoc

-- add_sub 

-- add_mul

-- add_mul-rev

-- mul_add

-- mul_sub-rev

-- add_div 

-- mul_div 

-- mul_div-rev

-- div_self


/- Power and square root rules. -/

-- div_pow_eq_mul_pow_neg

-- sqrt_eq_rpow


/- Exponential and logarithm rules. -/

-- exp_add (obj)
def expAddObj := 
  optimization (x y : ℝ)
    minimize (exp ((log x) + 2) : ℝ)
    subject to 
      hx : 0 < x

time_cmd reduction expAddObjRedAuto/expAddObjAuto : expAddObj := by
  unfold expAddObj
  convexify

-- exp_add (constr)
def expAddConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      hy : 0 < y
      h : exp ((log x) + 2) ≤ 10

time_cmd reduction expAddConstrRedAuto/expAddConstrAuto : expAddConstr := by
  unfold expAddConstr
  convexify

-- exp_sub 

-- exp_sub-rev

-- exp_mul

-- exp_mul-rev

-- exp_neg_eq_one_div-rev (obj)
def expNegEqOneDivRevObj := 
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to 
      h : 1 ≤ x

time_cmd reduction expNegEqOneDivRevObjRedAuto/expNegEqOneDivRevObjAuto : expNegEqOneDivRevObj := by
  unfold expNegEqOneDivRevObj
  convexify

#print expNegEqOneDivRevObjAuto

-- exp_neg_eq_one_div-rev (constr)
def expNegEqOneDivRevConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : 1 / (exp x) ≤ 1

-- exp_log 

-- log_mul 

-- log_div

-- log_exp

end Rules 