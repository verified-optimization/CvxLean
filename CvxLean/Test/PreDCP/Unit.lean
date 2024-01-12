import CvxLean.Command.Solve
import CvxLean.Command.Reduction
import CvxLean.Command.Equivalence
import CvxLean.Command.Util.TimeCmd
import CvxLean.Tactic.Basic.ChangeOfVariables
import CvxLean.Tactic.PreDCP.PreDCP

namespace Unit

noncomputable section

open CvxLean Minimization Real

/- Objective function rules. -/

-- map_objFun_log (obj)
-- NOTE: This works because an affine objective is prefered.
def mapObjFunLogObj :=
  optimization (x : ℝ)
    minimize (exp x)
    subject to
      h : 0 ≤ x

time_cmd equivalence mapObjFunLogObjRed/mapObjFunLogObjAuto : mapObjFunLogObj := by
  pre_dcp

#print mapObjFunLogObjAuto

-- map_objFun_sq (obj)
def mapObjFunSqObj :=
  optimization (x : ℝ)
    minimize (sqrt x)
    subject to
      h : 0 ≤ x

time_cmd equivalence mapObjFunSqObjRed/mapObjFunSqObjAuto : mapObjFunSqObj := by
  pre_dcp

#print mapObjFunSqObjAuto


/- Equality rules. -/

-- log_eq_log (constr)
def logEqLogConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : exp x = exp x

time_cmd equivalence logEqLogConstrRed/logEqLogConstrAuto : logEqLogConstr := by
  pre_dcp

#print logEqLogConstrAuto


/- Less than or equal rules. -/

-- le_sub_iff_add_le (constr)
-- NOTE: This uses le_sub_iff_add_le because 2 * x is preferred over x + x.
def leSubIffAddLeConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x ≤ 1 - x

time_cmd equivalence leSubIffAddLeConstrRed/leSubIffAddLeConstrAuto : leSubIffAddLeConstr := by
  pre_dcp

#print leSubIffAddLeConstrAuto

-- le_sub_iff_add_le-rev (constr)
def leSubIffAddLeConstrRev :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y + x ≤ x

time_cmd equivalence leSubIffAddLeConstrRevRed/leSubIffAddLeConstrRevAuto : leSubIffAddLeConstrRev := by
  pre_dcp

#print leSubIffAddLeConstrRevAuto

-- sub_le_iff_le_add (constr)
-- NOTE: same reasoning as le_sub_iff_add_le.
def subLeIffLeAddConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : 1 - x ≤ x

time_cmd equivalence subLeIffLeAddConstrRed/subLeIffLeAddConstrAuto : subLeIffLeAddConstr := by
  pre_dcp

#print subLeIffLeAddConstrAuto

-- sub_le_iff_le_add-rev (constr)
def subLeIffLeAddConstrRev :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x ≤ y + x

time_cmd equivalence subLeIffLeAddConstrRevRed/subLeIffLeAddConstrRevAuto : subLeIffLeAddConstrRev := by
  pre_dcp

#print subLeIffLeAddConstrRevAuto

-- div_le_iff (constr)
def divLeIffConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hy : 0 < y
      h : x / y ≤ 1

time_cmd equivalence divLeIffConstrRed/divLeIffConstrAuto : divLeIffConstr := by
  pre_dcp

#print divLeIffConstrAuto

-- div_le_iff-rev (constr)
def divLeIffRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hy : 0 < x
      h : x ≤ x * y

time_cmd equivalence divLeIffRevConstrRed/divLeIffRevConstrAuto : divLeIffRevConstr := by
  pre_dcp

#print divLeIffRevConstrAuto

-- log_le_log (constr)
def logLeLogConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      hy : 0 < y
      h : log x ≤ log y

time_cmd equivalence logLeLogConstrRed/logLeLogConstrAuto : logLeLogConstr := by
  pre_dcp

#print logLeLogConstrAuto

-- log_le_log-rev (constr)
def logLeLogRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : exp x ≤ exp y

time_cmd equivalence logLeLogRevConstrRed/logLeLogRevConstrAuto : logLeLogRevConstr := by
  pre_dcp

#print logLeLogRevConstrAuto

-- pow_two_le_pow_two (constr)
def powTwoLePowTwoConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      hy : 0 ≤ y
      h : x ^ (2 : ℝ) ≤ y ^ (2 : ℝ)

time_cmd equivalence powTwoLePowTwoConstrRed/powTwoLePowTwoConstrAuto : powTwoLePowTwoConstr := by
  pre_dcp

#print powTwoLePowTwoConstrAuto

-- pow_two_le_pow_two-rev (constr)
def powTwoLePowTwoRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      hy : 0 ≤ y
      h : sqrt x ≤ sqrt y

time_cmd equivalence powTwoLePowTwoRevConstrRed/powTwoLePowTwoRevConstrAuto : powTwoLePowTwoRevConstr := by
  pre_dcp

#print powTwoLePowTwoRevConstrAuto


/- Field rules -/

-- neg_neg (obj)
def negNegObj :=
  optimization (x : ℝ)
    minimize (-(-x) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence negNegObjRed/negNegObjAuto : negNegObj := by
  pre_dcp

#print negNegObjAuto

-- neg_neg (constr)
def negNegConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ -(-x)

time_cmd equivalence negNegConstrRed/negNegConstrAuto : negNegConstr := by
  pre_dcp

#print negNegConstrAuto

-- add_zero (obj)
def addZeroObj :=
  optimization (x : ℝ)
    minimize (x + 0 : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence addZeroObjRed/addZeroObjAuto : addZeroObj := by
  pre_dcp

#print addZeroObjAuto

-- add_zero (constr)
def addZeroConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ x + 0

time_cmd equivalence addZeroConstrRed/addZeroConstrAuto : addZeroConstr := by
  pre_dcp

#print addZeroConstrAuto

-- add_comm (obj)
-- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
def addCommObj :=
  optimization (x : ℝ)
    minimize (x + (1 + x) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence addCommObjRed/addCommObjAuto : addCommObj := by
  pre_dcp

#print addCommObjAuto

-- add_comm (constr)
-- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
def addCommConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : 0 < x
      hx : x + (1 + x) ≤ 1

time_cmd equivalence addCommConstrRed/addCommConstrAuto : addCommConstr := by
  pre_dcp

#print addCommConstrAuto

-- add_assoc (obj)
-- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
def addAssocObj :=
  optimization (x : ℝ)
    minimize (x + (x + 1) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence addAssocObjRed/addAssocObjAuto : addAssocObj := by
  pre_dcp

#print addAssocObjAuto

-- add_assoc (constr)
-- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
def addAssocConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x + (x + 1) ≤ 1

time_cmd equivalence addAssocConstrRed/addAssocConstrAuto : addAssocConstr := by
  pre_dcp

#print addAssocConstrAuto

-- sub_self (obj)
def subSelfObj :=
  optimization (x : ℝ)
    minimize (x - x : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence subSelfObjRed/subSelfObjAuto : subSelfObj := by
  pre_dcp

#print subSelfObjAuto

-- sub_self (constr)
def subSelfConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ x - x

time_cmd equivalence subSelfConstrRed/subSelfConstrAuto : subSelfConstr := by
  pre_dcp

#print subSelfConstrAuto

-- one_mul (obj)
def oneMulObj :=
  optimization (x : ℝ)
    minimize (1 * x : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence oneMulObjRed/oneMulObjAuto : oneMulObj := by
  pre_dcp

#print oneMulObjAuto

-- one_mul (constr)
def oneMulConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : 0 ≤ 1 * x

time_cmd equivalence oneMulConstrRed/oneMulConstrAuto : oneMulConstr := by
  pre_dcp

#print oneMulConstrAuto

-- one_mul-rev (obj)
-- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
def oneMulRevObj :=
  optimization (x : ℝ)
    minimize (x + x : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence oneMulRevObjRed/oneMulRevObjAuto : oneMulRevObj := by
  pre_dcp

#print oneMulRevObjAuto

-- one_mul-rev (constr)
-- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
def oneMulRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : 0 ≤ x + x

time_cmd equivalence oneMulRevConstrRed/oneMulRevConstrAuto : oneMulRevConstr := by
  pre_dcp

#print oneMulRevConstrAuto

-- mul_zero (obj)
def mulZeroObj :=
  optimization (x : ℝ)
    minimize (x * 0 : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence mulZeroObjRed/mulZeroObjAuto : mulZeroObj := by
  pre_dcp

#print mulZeroObjAuto

-- mul_zero (constr)
def mulZeroConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ x * 0

time_cmd equivalence mulZeroConstrRed/mulZeroConstrAuto : mulZeroConstr := by
  pre_dcp

#print mulZeroConstrAuto

-- mul_comm (obj)
-- NOTE: Empty domain here. Why?
def mulCommObj :=
  optimization (x y : ℝ)
    minimize (x * (y * (1 / x)) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulCommObjRed/mulCommObjAuto : mulCommObj := by
  pre_dcp

#print mulCommObjAuto

-- mul_comm (constr)
def mulCommConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : x * (y * (1 / x)) ≤ 1

time_cmd equivalence mulCommConstrRed/mulCommConstrAuto : mulCommConstr := by
  pre_dcp

#print mulCommConstrAuto

-- mul_assoc (obj)
def mulAssocObj :=
  optimization (x : ℝ)
    minimize (sqrt x * (sqrt x * 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulAssocObjRed/mulAssocObjAuto : mulAssocObj := by
  pre_dcp

#print mulAssocObjAuto

-- mul_assoc (constr)
def mulAssocConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : sqrt x * (sqrt x * 2) ≤ 1

time_cmd equivalence mulAssocConstrRed/mulAssocConstrAuto : mulAssocConstr := by
  pre_dcp

#print mulAssocConstrAuto

-- sub_eq_add_neg (obj)
def subEqAddNegObj :=
  optimization (x y : ℝ)
    minimize (x - (-y) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence subEqAddNegObjRed/subEqAddNegObjAuto : subEqAddNegObj := by
  pre_dcp

#print subEqAddNegObjAuto

-- sub_eq_add_neg (constr)
def subEqAddNegConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ x - (-x)

time_cmd equivalence subEqAddNegConstrRed/subEqAddNegConstrAuto : subEqAddNegConstr := by
  pre_dcp

#print subEqAddNegConstrAuto

-- sub_eq_add_neg-rev (obj)
def subEqAddNegRevObj :=
  optimization (x y : ℝ)
    minimize (x + (-y) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence subEqAddNegRevObjRed/subEqAddNegRevObjAuto : subEqAddNegRevObj := by
  pre_dcp

#print subEqAddNegRevObjAuto

-- sub_eq_add_neg-rev (constr)
def subEqAddNegRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ x + (-x)

time_cmd equivalence subEqAddNegRevConstrRed/subEqAddNegRevConstrAuto : subEqAddNegRevConstr := by
  pre_dcp

#print subEqAddNegRevConstrAuto

-- add_sub (obj)
def addSubObj :=
  optimization (x y : ℝ)
    minimize (x + (x - y) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence addSubObjRed/addSubObjAuto : addSubObj := by
  pre_dcp

#print addSubObjAuto

-- add_sub (constr)
def addSubConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h1 : 0 ≤ x
      h2 : x + (x - y) ≤ 1

time_cmd equivalence addSubConstrRed/addSubConstrAuto : addSubConstr := by
  pre_dcp

#print addSubConstrAuto

-- add_sub-rev (obj)
def addSubRevObj :=
  optimization (x : ℝ)
    minimize ((1 + x) - x : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence addSubRevObjRed/addSubRevObjAuto : addSubRevObj := by
  pre_dcp

#print addSubRevObjAuto

-- add_sub-rev (constr)
def addSubRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h1 : 0 ≤ x
      h2 : (1 + x) - x ≤ 1

time_cmd equivalence addSubRevConstrRed/addSubRevConstrAuto : addSubRevConstr := by
  pre_dcp

#print addSubRevConstrAuto

-- add_mul (obj)
def addMulObj :=
  optimization (x y : ℝ)
    minimize ((-1 + sqrt x) * sqrt x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence addMulObjRed/addMulObjAuto : addMulObj := by
  pre_dcp

#print addMulObjAuto

-- add_mul (constr)
def addMulConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (-1 + sqrt x) * sqrt x ≤ 1

time_cmd equivalence addMulConstrRed/addMulConstrAuto : addMulConstr := by
  pre_dcp

#print addMulConstrAuto

-- add_mul-rev (obj)
def addMulRevObj :=
  optimization (x : ℝ)
    minimize (2 * x + 3 * x : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence addMulRevObjRed/addMulRevObjAuto : addMulRevObj := by
  pre_dcp

#print addMulRevObjAuto

-- add_mul-rev (constr)
def addMulRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      h : 2 * x + 3 * x ≤ 1

time_cmd equivalence addMulRevConstrRed/addMulRevConstrAuto : addMulRevConstr := by
  pre_dcp

#print addMulRevConstrAuto

-- mul_add (obj)
def mulAddObj :=
  optimization (x : ℝ)
    minimize (sqrt x * (-1 + sqrt x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulAddObjRed/mulAddObjAuto : mulAddObj := by
  pre_dcp

#print mulAddObjAuto

-- mul_add (constr)
def mulAddConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : sqrt x * (-1 + sqrt x) ≤ 1

time_cmd equivalence mulAddConstrRed/mulAddConstrAuto : mulAddConstr := by
  pre_dcp

#print mulAddConstrAuto

-- mul_add-rev (obj)
def mulAddRevObj :=
    optimization (x : ℝ)
    minimize (x * 2 + x * 3 : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence mulAddRevObjRed/mulAddRevObjAuto : mulAddRevObj := by
  pre_dcp

#print mulAddRevObjAuto

-- mul_add-rev (constr)
def mulAddRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      h : x * 2 + x * 3 ≤ 1

time_cmd equivalence mulAddRevConstrRed/mulAddRevConstrAuto : mulAddRevConstr := by
  pre_dcp

#print mulAddRevConstrAuto

-- mul_sub (obj)
def mulSubObj :=
  optimization (x : ℝ)
    minimize (sqrt x * (sqrt x - 1) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulSubObjRed/mulSubObjAuto : mulSubObj := by
  pre_dcp

#print mulSubObjAuto

-- mul_sub (constr)
def mulSubConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : sqrt x * (sqrt x - 1) ≤ 1

time_cmd equivalence mulSubConstrRed/mulSubConstrAuto : mulSubConstr := by
  pre_dcp

#print mulSubConstrAuto

-- mul_sub-rev (obj)
def mulSubRevObj :=
  optimization (x : ℝ)
    minimize (x * 2 - x * 3 : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence mulSubRevObjRed/mulSubRevObjAuto : mulSubRevObj := by
  pre_dcp

#print mulSubRevObjAuto

-- mul_sub-rev (constr)
def mulSubRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      h : x * 2 - x * 3 ≤ 1

time_cmd equivalence mulSubRevConstrRed/mulSubRevConstrAuto : mulSubRevConstr := by
  pre_dcp

#print mulSubRevConstrAuto

-- add_div (obj)
def addDivObj :=
  optimization (x y : ℝ)
    minimize ((exp x + 1) / (exp y) : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence addDivObjRed/addDivObjAuto : addDivObj := by
  pre_dcp

#print addDivObjAuto

-- add_div (constr)
def addDivConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      hy : 0 < y
      h : (exp x + 1) / (exp y) ≤ 1

time_cmd equivalence addDivConstrRed/addDivConstrAuto : addDivConstr := by
  pre_dcp

#print addDivConstrAuto

-- add_div-rev (obj)
def addDivRevObj :=
  optimization (x : ℝ)
    minimize ((x / 2) + ((-x) / 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence addDivRevObjRed/addDivRevObjAuto : addDivRevObj := by
  pre_dcp

#print addDivRevObjAuto

-- add_div-rev (constr)
def addDivRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : (x / 2) + ((-x) / 2) ≤ x

time_cmd equivalence addDivRevConstrRed/addDivRevConstrAuto : addDivRevConstr := by
  pre_dcp

#print addDivRevConstrAuto

-- mul_div (obj)
def mulDivObj :=
  optimization (x y : ℝ)
    minimize ((sqrt x) * (sqrt x / 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulDivObjRed/mulDivObjAuto : mulDivObj := by
  pre_dcp

#print mulDivObjAuto

-- mul_div (constr)
def mulDivConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (sqrt x) * (sqrt x / 2) ≤ 1

time_cmd equivalence mulDivConstrRed/mulDivConstrAuto : mulDivConstr := by
  pre_dcp

#print mulDivConstrAuto

-- mul_div-rev (obj)
def mulDivRevObj :=
  optimization (x y : ℝ)
    minimize ((x * y) / x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulDivRevObjRed/mulDivRevObjAuto : mulDivRevObj := by
  pre_dcp

#print mulDivRevObjAuto

-- mul_div-rev (constr)
def mulDivRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (x * y) / x ≤ 1

time_cmd equivalence mulDivRevConstrRed/mulDivRevConstrAuto : mulDivRevConstr := by
  pre_dcp

#print mulDivRevConstrAuto

-- div_self (obj)
def divSelfObj :=
  optimization (x y : ℝ)
    minimize ((x / x) * y : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence divSelfObjRed/divSelfObjAuto : divSelfObj := by
  pre_dcp

#print divSelfObjAuto

-- div_self (constr)
def divSelfConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (x / x) * y ≤ 1

time_cmd equivalence divSelfConstrRed/divSelfConstrAuto : divSelfConstr := by
  pre_dcp

#print divSelfConstrAuto


/- Power and square root rules. -/

-- pow_add-rev (obj)
def powAddRevObj :=
  optimization (x : ℝ)
    minimize ((sqrt x) * (sqrt x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence powAddRevObjRed/powAddRevObjAuto : powAddRevObj := by
  pre_dcp

#print powAddRevObjAuto

-- pow_add-rev (constr)
def powAddRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (sqrt x) * (sqrt x) ≤ 1

time_cmd equivalence powAddRevConstrRed/powAddRevConstrAuto : powAddRevConstr := by
  pre_dcp

#print powAddRevConstrAuto

-- mul_pow (obj)
def mulPowObj :=
  optimization (x : ℝ)
    minimize ((x * (sqrt x)) ^ (2 : ℝ) / x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulPowObjRed/mulPowObjAuto : mulPowObj := by
  pre_dcp

#print mulPowObjAuto

-- mul_pow (constr)
def mulPowConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : ((x * (sqrt x)) ^ (2 : ℝ) / x) ≤ 1

time_cmd equivalence mulPowConstrRed/mulPowConstrAuto : mulPowConstr := by
  pre_dcp

#print mulPowConstrAuto

-- mul_pow-rev (obj)
def mulPowRevObj :=
  optimization (x : ℝ)
    minimize (((sqrt x) ^ (2 : ℝ)) * ((sqrt (x + 1)) ^ (2 : ℝ)) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulPowRevObjRed/mulPowRevObjAuto : mulPowRevObj := by
  pre_dcp

#print mulPowRevObjAuto

-- mul_pow-rev (constr)
def mulPowRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (((sqrt x) ^ (2 : ℝ)) * ((sqrt (x + 1)) ^ (2 : ℝ))) ≤ 1

time_cmd equivalence mulPowRevConstrRed/mulPowRevConstrAuto : mulPowRevConstr := by
  pre_dcp

#print mulPowRevConstrAuto

-- pow_mul-rev (obj)
def powMulRevObj :=
  optimization (x : ℝ)
    minimize ((x ^ (1 : ℝ)) ^ (2 : ℝ) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence powMulRevObjRed/powMulRevObjAuto : powMulRevObj := by
  pre_dcp

#print powMulRevObjAuto

-- pow_mul-rev (constr)
def powMulRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : ((x ^ (2 : ℝ)) ^ (2 : ℝ)) ≤ 1

time_cmd equivalence powMulRevConstrRed/powMulRevConstrAuto : powMulRevConstr := by
  pre_dcp

#print powMulRevConstrAuto

-- div_pow (obj)
def divPowObj :=
  optimization (x : ℝ)
    minimize ((x ^ (2 : ℝ)) * (1 / x) ^ (2 : ℝ) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence divPowObjRed/divPowObjAuto : divPowObj := by
  pre_dcp

#print divPowObjAuto

-- div_pow (constr)
def divPowConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (1 / x) ^ (2 : ℝ) ≤ 1

time_cmd equivalence divPowConstrRed/divPowConstrAuto : divPowConstr := by
  pre_dcp

#print divPowConstrAuto

-- div_pow-rev (obj)
def divPowRevObj :=
  optimization (x : ℝ)
    minimize ((x + x) ^ (2 : ℝ) / x ^ (2 : ℝ) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence divPowRevObjRed/divPowRevObjAuto : divPowRevObj := by
  pre_dcp

#print divPowRevObjAuto

-- div_pow-rev (constr)
def divPowRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : ((x + x) ^ (2 : ℝ) / x ^ (2 : ℝ)) ≤ x

time_cmd equivalence divPowRevConstrRed/divPowRevConstrAuto : divPowRevConstr := by
  pre_dcp

#print divPowRevConstrAuto

-- pow_sub-rev (obj)
def powSubRevObj :=
  optimization (x : ℝ)
    minimize ((x ^ (2 : ℝ)) / (sqrt x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence powSubRevObjRed/powSubRevObjAuto : powSubRevObj := by
  pre_dcp

#print powSubRevObjAuto

-- pow_sub-rev (constr)
def powSubRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : ((x ^ (2 : ℝ)) / (sqrt x)) ≤ 1

time_cmd equivalence powSubRevConstrRed/powSubRevConstrAuto : powSubRevConstr := by
  pre_dcp

#print powSubRevConstrAuto

-- div_pow_eq_mul_pow_neg (obj)
def divPowEqMulPowNegObj :=
  optimization (x : ℝ)
    minimize (1 / (x ^ (2 : ℝ)) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence divPowEqMulPowNegObjRed/divPowEqMulPowNegObjAuto : divPowEqMulPowNegObj := by
  pre_dcp

#print divPowEqMulPowNegObjAuto

-- div_pow_eq_mul_pow_neg (constr)
def divPowEqMulPowNegConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : 1 / (x ^ (2 : ℝ)) ≤ 1

time_cmd equivalence divPowEqMulPowNegConstrRed/divPowEqMulPowNegConstrAuto : divPowEqMulPowNegConstr := by
  pre_dcp

#print divPowEqMulPowNegConstrAuto

-- one_div_eq_pow_neg_one (obj)
def oneDivEqPowNegOneObj :=
  optimization (x : ℝ)
    minimize (1 / (sqrt x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence oneDivEqPowNegOneObjRed/oneDivEqPowNegOneObjAuto : oneDivEqPowNegOneObj := by
  pre_dcp

#print oneDivEqPowNegOneObjAuto

-- one_div_eq_pow_neg_one (constr)
def oneDivEqPowNegOneConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : 1 / (sqrt x) ≤ 1

time_cmd equivalence oneDivEqPowNegOneConstrRed/oneDivEqPowNegOneConstrAuto : oneDivEqPowNegOneConstr := by
  pre_dcp

#print oneDivEqPowNegOneConstrAuto

-- sqrt_eq_rpow (obj)
def sqrtEqRpowObj :=
  optimization (x : ℝ)
    minimize ((sqrt x) * (sqrt x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence sqrtEqRpowObjRed/sqrtEqRpowObjAuto : sqrtEqRpowObj := by
  pre_dcp

#print sqrtEqRpowObjAuto

-- sqrt_eq_rpow (constr)
def sqrtEqRpowConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (sqrt x) * (sqrt x) ≤ 1

time_cmd equivalence sqrtEqRpowConstrRed/sqrtEqRpowConstrAuto : sqrtEqRpowConstr := by
  pre_dcp

#print sqrtEqRpowConstrAuto

-- pow_half_two (obj)
def powHalfTwoObj :=
  optimization (x : ℝ)
    minimize ((sqrt x) ^ (2 : ℝ) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence powHalfTwoObjRed/powHalfTwoObjAuto : powHalfTwoObj := by
  pre_dcp

#print powHalfTwoObjAuto

-- pow_half_two (constr)
def powHalfTwoConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (sqrt x) ^ (2 : ℝ) ≤ 1

time_cmd equivalence powHalfTwoConstrRed/powHalfTwoConstrAuto : powHalfTwoConstr := by
  pre_dcp

#print powHalfTwoConstrAuto


/- Exponential and logarithm rules. -/

-- exp_add (obj)
def expAddObj :=
  optimization (x : ℝ)
    minimize (exp ((log x) + 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expAddObjRed/expAddObjAuto : expAddObj := by
  pre_dcp

#print expAddObjAuto

-- exp_add (constr)
def expAddConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp ((log x) + 2) ≤ 10

time_cmd equivalence expAddConstrRed/expAddConstrAuto : expAddConstr := by
  pre_dcp

#print expAddConstrAuto

-- exp_add-rev (obj)
def expAddRevObj :=
  optimization (x y : ℝ)
    minimize (exp x * exp x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expAddRevObjRed/expAddRevObjAuto : expAddRevObj := by
  pre_dcp

#print expAddRevObjAuto

-- exp_add-rev (constr)
def expAddRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp x * exp x ≤ 1

time_cmd equivalence expAddRevConstrRed/expAddRevConstrAuto : expAddRevConstr := by
  pre_dcp

#print expAddRevConstrAuto

-- exp_sub (obj)
def expSubObj :=
  optimization (x : ℝ)
    minimize (exp ((log x) - 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expSubObjRed/expSubObjAuto : expSubObj := by
  pre_dcp

#print expSubObjAuto

-- exp_sub (constr)
def expSubConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp ((log x) - 2) ≤ 1

time_cmd equivalence expSubConstrRed/expSubConstrAuto : expSubConstr := by
  pre_dcp

#print expSubConstrAuto

-- exp_sub-rev (obj)
def expSubRevObj :=
  optimization (x y : ℝ)
    minimize (exp (2 * x) / exp x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expSubRevObjRed/expSubRevObjAuto : expSubRevObj := by
  pre_dcp

#print expSubRevObjAuto

-- exp_sub-rev (constr)
def expSubRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp (2 * x) / exp x ≤ 1

time_cmd equivalence expSubRevConstrRed/expSubRevConstrAuto : expSubRevConstr := by
  pre_dcp

#print expSubRevConstrAuto

-- exp_mul (obj)
def expMulObj :=
  optimization (x : ℝ)
    minimize (exp (log x * 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expMulObjRed/expMulObjAuto : expMulObj := by
  pre_dcp

#print expMulObjAuto

-- exp_mul (constr)
def expMulConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp (log x * 2) ≤ 1

time_cmd equivalence expMulConstrRed/expMulConstrAuto : expMulConstr := by
  pre_dcp

#print expMulConstrAuto

-- exp_mul-rev (obj)
def expMulRevObj :=
  optimization (x : ℝ)
    minimize ((exp x) ^ (2 : ℝ) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expMulRevObjRed/expMulRevObjAuto : expMulRevObj := by
  pre_dcp

#print expMulRevObjAuto

-- exp_mul-rev (constr)
def expMulRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : ((exp x) ^ (2 : ℝ)) ≤ 1

time_cmd equivalence expMulRevConstrRed/expMulRevConstrAuto : expMulRevConstr := by
  pre_dcp

#print expMulRevConstrAuto

-- exp_neg_eq_one_div (obj)
def expNegEqOneDivObj :=
  optimization (x : ℝ)
    minimize (x * exp (-(log x)) : ℝ)
    subject to
      h : 1 ≤ x

time_cmd equivalence expNegEqOneDivObjRed/expNegEqOneDivObjAuto : expNegEqOneDivObj := by
  pre_dcp

#print expNegEqOneDivObjAuto

-- exp_neg_eq_one_div (constr)
def expNegEqOneDivConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : x * exp (-(log x)) ≤ x

time_cmd equivalence expNegEqOneDivConstrRed/expNegEqOneDivConstrAuto : expNegEqOneDivConstr := by
  pre_dcp

#print expNegEqOneDivConstrAuto

-- exp_neg_eq_one_div-rev (obj)
def expNegEqOneDivRevObj :=
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to
      h : 1 ≤ x

time_cmd equivalence expNegEqOneDivRevObjRed/expNegEqOneDivRevObjAuto : expNegEqOneDivRevObj := by
  pre_dcp

#print expNegEqOneDivRevObjAuto

-- exp_neg_eq_one_div-rev (constr)
def expNegEqOneDivRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : 1 / (exp x) ≤ 1

time_cmd equivalence expNegEqOneDivRevConstrRed/expNegEqOneDivRevConstrAuto : expNegEqOneDivRevConstr := by
  pre_dcp

#print expNegEqOneDivRevConstrAuto

-- log_mul (obj)
def logMulObj :=
  optimization (x : ℝ)
    minimize (- log (x * x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence logMulObjRed/logMulObjAuto : logMulObj := by
  pre_dcp

#print logMulObjAuto

-- log_mul (constr)
def logMulConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : 1 ≤ log (x * x)

time_cmd equivalence logMulConstrRed/logMulConstrAuto : logMulConstr := by
  pre_dcp

#print logMulConstrAuto

-- log_mul-rev (obj)
def logMulRevObj :=
  optimization (x : ℝ)
    minimize (exp (log x + log (x + 1)))
    subject to
      hx : 0 < x

time_cmd equivalence logMulRevObjRed/logMulRevObjAuto : logMulRevObj := by
  pre_dcp

#print logMulRevObjAuto

-- log_mul-rev (constr)
def logMulRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp (log x + log (x + 1)) ≤ 1

time_cmd equivalence logMulRevConstrRed/logMulRevConstrAuto : logMulRevConstr := by
  pre_dcp

#print logMulRevConstrAuto

-- log_div (obj)
def logDivObj :=
  optimization (x : ℝ)
    minimize (log ((exp x) / x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence logDivObjRed/logDivObjAuto : logDivObj := by
  pre_dcp

#print logDivObjAuto

-- log_div (constr)
def logDivConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : log ((exp x) / x) ≤ 1

time_cmd equivalence logDivConstrRed/logDivConstrAuto : logDivConstr := by
  pre_dcp

#print logDivConstrAuto

-- log_div-rev (obj)
def logDivRevObj :=
  optimization (x : ℝ)
    minimize (- (log (x ^ (2 : ℝ)) - log x))
    subject to
      hx : 0 < x

time_cmd equivalence logDivRevObjRed/logDivRevObjAuto : logDivRevObj := by
  pre_dcp

#print logDivRevObjAuto

-- log_div-rev (constr)
def logDivRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : - (log (x ^ (2 : ℝ)) - log x) ≤ 1

time_cmd equivalence logDivRevConstrRed/logDivRevConstrAuto : logDivRevConstr := by
  pre_dcp

#print logDivRevConstrAuto

-- exp_log (obj)
def expLogObj :=
  optimization (x : ℝ)
    minimize (exp (log x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expLogObjRed/expLogObjAuto : expLogObj := by
  pre_dcp

#print expLogObjAuto

-- exp_log (constr)
def expLogConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : exp (log x) ≤ 1

time_cmd equivalence expLogConstrRed/expLogConstrAuto : expLogConstr := by
  pre_dcp

#print expLogConstrAuto

-- log_exp (obj)
def logExpObj :=
  optimization (x : ℝ)
    minimize (log (exp x) : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence logExpObjRed/logExpObjAuto : logExpObj := by
  pre_dcp

#print logExpObjAuto

-- log_exp (constr)
def logExpConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : log (exp x) ≤ 1

time_cmd equivalence logExpConstrRed/logExpConstrAuto : logExpConstr := by
  pre_dcp

#print logExpConstrAuto

end

end Unit
