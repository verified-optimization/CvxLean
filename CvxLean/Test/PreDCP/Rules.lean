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

#check log_eq_log

reduction logEqLogConstrRedAuto/logEqLogConstrAuto : logEqLogConstr := by
  unfold logEqLogConstr
  convexify

#print logEqLogConstrAuto


/- Less than or equal rules. -/

-- le_sub_iff_add_le

def leSubIffAddLeConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x ≤ 1 - x

reduction leSubIffAddLeConstrRedAuto/leSubIffAddLeConstrAuto : leSubIffAddLeConstr := by 
  unfold leSubIffAddLeConstr
  convexify

#print leSubIffAddLeConstrAuto

-- log_le_log
def logLeLogConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      hx : 0 < x
      hy : 0 < y
      h : log x ≤ log y

#check log_le_log

reduction logLeLogConstrRedAuto/logLeLogConstrAuto : logLeLogConstr := by
  unfold logLeLogConstr
  convexify

-- TODO(RFM): The rest.

def invExpObj := 
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to 
      h : 1 ≤ x

time_cmd reduction invExpObjRedAuto/invExpObjAuto : invExpObj := by
  unfold invExpObj
  convexify
  exact done

def invExpConstr := 
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : 1 / (exp x) ≤ 1

def mulExpObj := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : (exp x) * (exp y) ≤ 1
      hx : 1 ≤ x
      hy : 1 ≤ y

def mulExpConstr := 
  optimization (x y : ℝ)
    minimize ((exp x) * (exp y))
    subject to 
      hx : 1 ≤ x
      hy : 1 ≤ y

def leMulRevConstr := False

def logExpObj := False 

def logExpConstr := False

def logDivObj := False 

def logDivConstr := False

def logMulObj := False 

def logMulConstr := False 

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