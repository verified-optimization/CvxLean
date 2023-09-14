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

time_cmd equivalence logEqLogConstrRed/logEqLogConstrAuto : logEqLogConstr := by
  unfold logEqLogConstr
  convexify

#print logEqLogConstrAuto


/- Less than or equal rules. -/

-- le_sub_iff_add_le
-- NOTE(RFM): This uses le_sub_iff_add_le because 2 * x is preferred over x + x.
def leSubIffAddLeConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x ≤ 1 - x

time_cmd equivalence leSubIffAddLeConstrRed/leSubIffAddLeConstrAuto : leSubIffAddLeConstr := by 
  unfold leSubIffAddLeConstr
  convexify

#print leSubIffAddLeConstrAuto

-- le_sub_iff_add_le-rev
def leSubIffAddLeConstrRev := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y + x ≤ x

time_cmd equivalence leSubIffAddLeConstrRevRed/leSubIffAddLeConstrRevAuto : leSubIffAddLeConstrRev := by
  unfold leSubIffAddLeConstrRev
  convexify

#print leSubIffAddLeConstrRevAuto

-- div_le_iff
def divLeIffConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hy : 0 < y
      h : x / y ≤ 1
  
time_cmd equivalence divLeIffConstrRed/divLeIffConstrAuto : divLeIffConstr := by
  unfold divLeIffConstr
  convexify

#print divLeIffConstrAuto

-- div_le_iff-rev 
def divLeIffRevConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hy : 0 < x
      h : x ≤ x * y

time_cmd equivalence divLeIffRevConstrRed/divLeIffRevConstrAuto : divLeIffRevConstr := by
  unfold divLeIffRevConstr
  convexify

#print divLeIffRevConstrAuto

-- log_le_log
def logLeLogConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      hy : 0 < y
      h : log x ≤ log y

time_cmd equivalence logLeLogConstrRed/logLeLogConstrAuto : logLeLogConstr := by
  unfold logLeLogConstr
  convexify

#print logLeLogConstrAuto

-- log_le_log-rev
def logLeLogRevConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : exp x ≤ exp y

time_cmd equivalence logLeLogRevConstrRed/logLeLogRevConstrAuto : logLeLogRevConstr := by
  unfold logLeLogRevConstr
  convexify

#print logLeLogRevConstrAuto


/- Field rules -/

-- add_comm (obj)
-- NOTE(RFM): This uses one_mul-rev because 2 * x is preferred over x + x.
def addCommObj := 
  optimization (x : ℝ)
    minimize (x + (1 + x) : ℝ)
    subject to 
      h : 0 ≤ x

time_cmd equivalence addCommObjRed/addCommObjAuto : addCommObj := by
  unfold addCommObj
  convexify

#print addCommObjAuto

-- add_comm (constr)
-- NOTE(RFM): This uses one_mul-rev because 2 * x is preferred over x + x.
def addCommConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : 0 < x
      hx : x + (1 + x) ≤ 1

time_cmd equivalence addCommConstrRed/addCommConstrAuto : addCommConstr := by
  unfold addCommConstr
  convexify

#print addCommConstrAuto

-- add_assoc (obj)
-- NOTE(RFM): This uses one_mul-rev because 2 * x is preferred over x + x.
def addAssocObj := 
  optimization (x : ℝ)
    minimize (x + (x + 1) : ℝ)
    subject to 
      h : 0 ≤ x

time_cmd equivalence addAssocObjRed/addAssocObjAuto : addAssocObj := by
  unfold addAssocObj
  convexify

#print addAssocObjAuto

-- add_assoc (constr)
-- NOTE(RFM): This uses one_mul-rev because 2 * x is preferred over x + x.
def addAssocConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : x + (x + 1) ≤ 1

time_cmd equivalence addAssocConstrRed/addAssocConstrAuto : addAssocConstr := by
  unfold addAssocConstr
  convexify

#print addAssocConstrAuto

-- sub_self (obj)
def subSelfObj := 
  optimization (x : ℝ)
    minimize (x - x : ℝ)
    subject to 
      h : 0 ≤ x

time_cmd equivalence subSelfObjRed/subSelfObjAuto : subSelfObj := by
  unfold subSelfObj
  convexify

#print subSelfObjAuto

-- sub_self (constr)
def subSelfConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : y ≤ x - x

time_cmd equivalence subSelfConstrRed/subSelfConstrAuto : subSelfConstr := by
  unfold subSelfConstr
  convexify

#print subSelfConstrAuto

-- mul_zero (obj)
def mulZeroObj := 
  optimization (x : ℝ)
    minimize (x * 0 : ℝ)
    subject to 
      h : 0 ≤ x

time_cmd equivalence mulZeroObjRed/mulZeroObjAuto : mulZeroObj := by
  unfold mulZeroObj
  convexify

#print mulZeroObjAuto

-- mul_zero (constr)
def mulZeroConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : y ≤ x * 0

time_cmd equivalence mulZeroConstrRed/mulZeroConstrAuto : mulZeroConstr := by
  unfold mulZeroConstr
  convexify

#print mulZeroConstrAuto

-- one_mul (obj)
def oneMulObj := 
  optimization (x : ℝ)
    minimize (1 * x : ℝ)
    subject to 
      h : 0 ≤ x

time_cmd equivalence oneMulObjRed/oneMulObjAuto : oneMulObj := by
  unfold oneMulObj
  convexify

#print oneMulObjAuto

-- one_mul (constr)
def oneMulConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : 0 ≤ 1 * x

time_cmd equivalence oneMulConstrRed/oneMulConstrAuto : oneMulConstr := by
  unfold oneMulConstr
  convexify

#print oneMulConstrAuto

-- one_mul-rev (obj)
-- NOTE(RFM): This uses one_mul-rev because 2 * x is preferred over x + x.
def oneMulRevObj := 
  optimization (x : ℝ)
    minimize (x + x : ℝ)
    subject to 
      h : 0 ≤ x

time_cmd equivalence oneMulRevObjRed/oneMulRevObjAuto : oneMulRevObj := by
  unfold oneMulRevObj
  convexify

#print oneMulRevObjAuto

-- one_mul-rev (constr)
-- NOTE(RFM): This uses one_mul-rev because 2 * x is preferred over x + x.
def oneMulRevConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : 0 ≤ x + x

time_cmd equivalence oneMulRevConstrRed/oneMulRevConstrAuto : oneMulRevConstr := by
  unfold oneMulRevConstr
  convexify

#print oneMulRevConstrAuto

-- mul_comm (obj)

def mulCommObj := 
  optimization (x y : ℝ)
    minimize (x * (y * (1 / x)) : ℝ)
    subject to 
      hx : 0 < x

time_cmd equivalence mulCommObjRed/mulCommObjAuto : mulCommObj := by
  unfold mulCommObj
  convexify

#print mulCommObjAuto

-- mul_comm (constr)
def mulCommConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      h : x * (y * (1 / x)) ≤ 1

time_cmd equivalence mulCommConstrRed/mulCommConstrAuto : mulCommConstr := by
  unfold mulCommConstr
  convexify

#print mulCommConstrAuto

-- mul_assoc (obj)
def mulAssocObj := 
  optimization (x : ℝ)
    minimize (exp x * (exp x * 2) : ℝ)
    subject to 
      hx : 0 < x

time_cmd equivalence mulAssocObjRed/mulAssocObjAuto : mulAssocObj := by
  convexify

#print mulAssocObjAuto

-- mul_assoc (constr)
def mulAssocConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      h : exp x * (exp x * 2) ≤ 1

time_cmd equivalence mulAssocConstrRed/mulAssocConstrAuto : mulAssocConstr := by
  unfold mulAssocConstr
  convexify

#print mulAssocConstrAuto

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

time_cmd equivalence expAddObjRed/expAddObjAuto : expAddObj := by
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

time_cmd equivalence expAddConstrRed/expAddConstrAuto : expAddConstr := by
  unfold expAddConstr
  convexify

-- exp_sub 

-- exp_sub-rev

-- exp_mul

-- exp_mul-rev

-- exp_neg_eq_one_div-rev (obj)
-- def expNegEqOneDivRevObj := 
--   optimization (x : ℝ)
--     minimize (1 / (exp x))
--     subject to 
--       h : 1 ≤ x

-- time_cmd equivalence expNegEqOneDivRevObjRed/expNegEqOneDivRevObjAuto : expNegEqOneDivRevObj := by
--   unfold expNegEqOneDivRevObj
--   convexify

-- #print expNegEqOneDivRevObjAuto

-- -- exp_neg_eq_one_div-rev (constr)
-- def expNegEqOneDivRevConstr := 
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to 
--       h : 1 / (exp x) ≤ 1

-- exp_log 

-- log_mul 

-- log_div

-- log_exp

end Rules 