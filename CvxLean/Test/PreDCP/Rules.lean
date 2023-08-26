import CvxLean.Command.Solve
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

time_cmd reduction logEqLogConstrRedAuto/logEqLogConstrAuto : logEqLogConstr := by
  unfold logEqLogConstr
  convexify


/- Less than or equal rules. -/

-- le_sub_iff_add_le (TODO)
def leSubIffAddLeConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x ≤ 1 - x

time_cmd reduction leSubIffAddLeConstrRedAuto/leSubIffAddLeConstrAuto : leSubIffAddLeConstr := by 
  unfold leSubIffAddLeConstr
  convexify

-- div_le_iff (TODO)

-- div_le_one-rev (TODO)

-- log_le_log
def logLeLogConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      hy : 0 < y
      h : log x ≤ log y

time_cmd reduction logLeLogConstrRedAuto/logLeLogConstrAuto : logLeLogConstr := by
  unfold logLeLogConstr
  convexify

-- log_le_log-rev (TODO)
def logLeLogRevConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : exp x ≤ exp y

reduction logLeLogRevConstrRedAuto/logLeLogRevConstrAuto : logLeLogRevConstr := by
  unfold logLeLogRevConstr
  convexify

/- Field rules -/


/- Power and square root rules. -/



/- Exponential and logarithm rules. -/

-- exp_add
def expAddConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : exp (x + y) ≤ exp x

-- exp_add

-- exp_neg_eq_one_div-rev
def expNegEqOneDivRevObj := 
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to 
      h : 1 ≤ x

time_cmd reduction expNegEqOneDivRevObjRedAuto/expNegEqOneDivRevObjAuto : expNegEqOneDivRevObj := by
  unfold expNegEqOneDivRevObj
  convexify

-- exp_neg_eq_one_div-rev
def expNegEqOneDivRevConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : 1 / (exp x) ≤ 1

def leMulRevConstr := False

def logExpObj := False 

def logExpConstr := False

def logDivObj := False 

def logDivConstr := False

def logMulObj := False 

def powExpObj := False 

def powExpConstr := False 

def divExpObj := False 

def divExpConstr := False 

def addAssocObj := False 

def addAssocConstr := False 

def addMulObj := False

def addMulConstr := False

def addSubObj := False 

def addSubConstr := False 

def divAddObj := False 

def divAddConstr := False 

def subMulLeftObj := False 

def subMulLeftConstr := False

def divPowObj := False

def divPowConstr := False

def mulCommObj := False 

def mulCommConstr := False 

def mulAssocObj := False 

def mulAssocConstr := False

def mulAddObj := False

def mulAddConstr := False

def addCommObj := False

def addCommConstr := False

def mulDivObj := False 

def mulDivConstr := False

def divMulObj := False

def divMulConstr := False

def sqrtEqRPowObj := False

def sqrtEqRPowConstr := False

def leDivOneConstr := False 

def mapObjfunLogObj := False

end Rules 