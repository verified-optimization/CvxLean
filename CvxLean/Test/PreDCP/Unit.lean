import CvxLean.Command.Solve
import CvxLean.Command.Equivalence
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Test.Util.TimeCmd

noncomputable section Rules

open CvxLean Minimization Real

-- /- Objective function rules. -/

-- -- map_objFun_log (obj)
-- -- NOTE: This works because an affine objective is prefered.
-- def mapObjFunLogObj :=
--   optimization (x : ℝ)
--     minimize (exp x)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence mapObjFunLogObjRed/mapObjFunLogObjAuto : mapObjFunLogObj := by
--   convexify

-- #print mapObjFunLogObjAuto

-- -- map_objFun_sq (obj)
-- def mapObjFunSqObj :=
--   optimization (x : ℝ)
--     minimize (sqrt x)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence mapObjFunSqObjRed/mapObjFunSqObjAuto : mapObjFunSqObj := by
--   convexify

-- #print mapObjFunSqObjAuto


-- /- Equality rules. -/

-- -- log_eq_log (constr)
-- def logEqLogConstr :=
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : exp x = exp x

-- time_cmd equivalence logEqLogConstrRed/logEqLogConstrAuto : logEqLogConstr := by
--   convexify

-- #print logEqLogConstrAuto


-- /- Less than or equal rules. -/

-- -- le_sub_iff_add_le (constr)
-- -- NOTE: This uses le_sub_iff_add_le because 2 * x is preferred over x + x.
-- def leSubIffAddLeConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : x ≤ 1 - x

-- time_cmd equivalence leSubIffAddLeConstrRed/leSubIffAddLeConstrAuto : leSubIffAddLeConstr := by
--   convexify

-- #print leSubIffAddLeConstrAuto

-- -- le_sub_iff_add_le-rev (constr)
-- def leSubIffAddLeConstrRev :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : y + x ≤ x

-- time_cmd equivalence leSubIffAddLeConstrRevRed/leSubIffAddLeConstrRevAuto : leSubIffAddLeConstrRev := by
--   convexify

-- #print leSubIffAddLeConstrRevAuto

-- -- sub_le_iff_le_add (constr)
-- -- NOTE: same reasoning as le_sub_iff_add_le.
-- def subLeIffLeAddConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : 1 - x ≤ x

-- time_cmd equivalence subLeIffLeAddConstrRed/subLeIffLeAddConstrAuto : subLeIffLeAddConstr := by
--   convexify

-- #print subLeIffLeAddConstrAuto

-- -- sub_le_iff_le_add-rev (constr)
-- def subLeIffLeAddConstrRev :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : x ≤ y + x

-- time_cmd equivalence subLeIffLeAddConstrRevRed/subLeIffLeAddConstrRevAuto : subLeIffLeAddConstrRev := by
--   convexify

-- #print subLeIffLeAddConstrRevAuto

-- -- div_le_iff (constr)
-- def divLeIffConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hy : 0 < y
--       h : x / y ≤ 1

-- time_cmd equivalence divLeIffConstrRed/divLeIffConstrAuto : divLeIffConstr := by
--   convexify

-- #print divLeIffConstrAuto

-- -- div_le_iff-rev (constr)
-- def divLeIffRevConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hy : 0 < x
--       h : x ≤ x * y

-- time_cmd equivalence divLeIffRevConstrRed/divLeIffRevConstrAuto : divLeIffRevConstr := by
--   convexify

-- #print divLeIffRevConstrAuto

-- -- log_le_log (constr)
-- def logLeLogConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hx : 0 < x
--       hy : 0 < y
--       h : log x ≤ log y

-- time_cmd equivalence logLeLogConstrRed/logLeLogConstrAuto : logLeLogConstr := by
--   convexify

-- #print logLeLogConstrAuto

-- -- log_le_log-rev (constr)
-- def logLeLogRevConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : exp x ≤ exp y

-- time_cmd equivalence logLeLogRevConstrRed/logLeLogRevConstrAuto : logLeLogRevConstr := by
--   convexify

-- #print logLeLogRevConstrAuto

-- -- pow_two_le_pow_two (constr)
-- def powTwoLePowTwoConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hx : 0 ≤ x
--       hy : 0 ≤ y
--       h : x ^ 2 ≤ y ^ 2

-- time_cmd equivalence powTwoLePowTwoConstrRed/powTwoLePowTwoConstrAuto : powTwoLePowTwoConstr := by
--   convexify

-- #print powTwoLePowTwoConstrAuto

-- -- pow_two_le_pow_two-rev (constr)
-- def powTwoLePowTwoRevConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hx : 0 ≤ x
--       hy : 0 ≤ y
--       h : sqrt x ≤ sqrt y

-- time_cmd equivalence powTwoLePowTwoRevConstrRed/powTwoLePowTwoRevConstrAuto : powTwoLePowTwoRevConstr := by
--   convexify

-- #print powTwoLePowTwoRevConstrAuto


-- /- Field rules -/

-- neg_neg (obj)
def negNegObj :=
  optimization (x : ℝ)
    minimize (-(-x) : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence negNegObjRed/negNegObjAuto : negNegObj := by
  convexify

#print negNegObjAuto

-- neg_neg (constr)
def negNegConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ -(-x)

time_cmd equivalence negNegConstrRed/negNegConstrAuto : negNegConstr := by
  convexify

#print negNegConstrAuto

-- -- add_zero (obj)
-- def addZeroObj :=
--   optimization (x : ℝ)
--     minimize (x + 0 : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence addZeroObjRed/addZeroObjAuto : addZeroObj := by
--   convexify

-- #print addZeroObjAuto

-- -- add_zero (constr)
-- def addZeroConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : y ≤ x + 0

-- time_cmd equivalence addZeroConstrRed/addZeroConstrAuto : addZeroConstr := by
--   convexify

-- #print addZeroConstrAuto

-- -- add_comm (obj)
-- -- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
-- def addCommObj :=
--   optimization (x : ℝ)
--     minimize (x + (1 + x) : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence addCommObjRed/addCommObjAuto : addCommObj := by
--   convexify

-- #print addCommObjAuto

-- -- add_comm (constr)
-- -- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
-- def addCommConstr :=
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : 0 < x
--       hx : x + (1 + x) ≤ 1

-- time_cmd equivalence addCommConstrRed/addCommConstrAuto : addCommConstr := by
--   convexify

-- #print addCommConstrAuto

-- -- add_assoc (obj)
-- -- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
-- def addAssocObj :=
--   optimization (x : ℝ)
--     minimize (x + (x + 1) : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence addAssocObjRed/addAssocObjAuto : addAssocObj := by
--   convexify

-- #print addAssocObjAuto

-- -- add_assoc (constr)
-- -- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
-- def addAssocConstr :=
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : x + (x + 1) ≤ 1

-- time_cmd equivalence addAssocConstrRed/addAssocConstrAuto : addAssocConstr := by
--   convexify

-- #print addAssocConstrAuto

-- -- sub_self (obj)
-- def subSelfObj :=
--   optimization (x : ℝ)
--     minimize (x - x : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence subSelfObjRed/subSelfObjAuto : subSelfObj := by
--   convexify

-- #print subSelfObjAuto

-- -- sub_self (constr)
-- def subSelfConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : y ≤ x - x

-- time_cmd equivalence subSelfConstrRed/subSelfConstrAuto : subSelfConstr := by
--   convexify

-- #print subSelfConstrAuto

-- -- one_mul (obj)
-- def oneMulObj :=
--   optimization (x : ℝ)
--     minimize (1 * x : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence oneMulObjRed/oneMulObjAuto : oneMulObj := by
--   convexify

-- #print oneMulObjAuto

-- -- one_mul (constr)
-- def oneMulConstr :=
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : 0 ≤ 1 * x

-- time_cmd equivalence oneMulConstrRed/oneMulConstrAuto : oneMulConstr := by
--   convexify

-- #print oneMulConstrAuto

-- -- one_mul-rev (obj)
-- -- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
-- def oneMulRevObj :=
--   optimization (x : ℝ)
--     minimize (x + x : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence oneMulRevObjRed/oneMulRevObjAuto : oneMulRevObj := by
--   convexify

-- #print oneMulRevObjAuto

-- -- one_mul-rev (constr)
-- -- NOTE: This uses one_mul-rev because 2 * x is preferred over x + x.
-- def oneMulRevConstr :=
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : 0 ≤ x + x

-- time_cmd equivalence oneMulRevConstrRed/oneMulRevConstrAuto : oneMulRevConstr := by
--   convexify

-- #print oneMulRevConstrAuto

-- -- mul_zero (obj)
-- def mulZeroObj :=
--   optimization (x : ℝ)
--     minimize (x * 0 : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence mulZeroObjRed/mulZeroObjAuto : mulZeroObj := by
--   convexify

-- #print mulZeroObjAuto

-- -- mul_zero (constr)
-- def mulZeroConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       h : y ≤ x * 0

-- time_cmd equivalence mulZeroConstrRed/mulZeroConstrAuto : mulZeroConstr := by
--   convexify

-- #print mulZeroConstrAuto

-- -- mul_comm (obj)

-- def mulCommObj :=
--   optimization (x y : ℝ)
--     minimize (x * (y * (1 / x)) : ℝ)
--     subject to
--       hx : 0 < x

-- time_cmd equivalence mulCommObjRed/mulCommObjAuto : mulCommObj := by
--   convexify

-- #print mulCommObjAuto

-- -- mul_comm (constr)
-- def mulCommConstr :=
--   optimization (x y : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hx : 0 < x
--       h : x * (y * (1 / x)) ≤ 1

-- time_cmd equivalence mulCommConstrRed/mulCommConstrAuto : mulCommConstr := by
--   convexify

-- #print mulCommConstrAuto

-- -- mul_assoc (obj)
-- def mulAssocObj :=
--   optimization (x : ℝ)
--     minimize (sqrt x * (sqrt x * 2) : ℝ)
--     subject to
--       hx : 0 < x

-- time_cmd equivalence mulAssocObjRed/mulAssocObjAuto : mulAssocObj := by
--   convexify

-- #print mulAssocObjAuto

-- -- mul_assoc (constr)
-- def mulAssocConstr :=
--   optimization (x : ℝ)
--     minimize (0 : ℝ)
--     subject to
--       hx : 0 < x
--       h : sqrt x * (sqrt x * 2) ≤ 1

-- time_cmd equivalence mulAssocConstrRed/mulAssocConstrAuto : mulAssocConstr := by
--   convexify

-- #print mulAssocConstrAuto

-- sub_eq_add_neg (obj)
def subEqAddNegObj :=
  optimization (x y : ℝ)
    minimize (x - (-y) : ℝ)
    subject to
      h : 0 ≤ x

#check neg_neg

time_cmd equivalence subEqAddNegObjRed/subEqAddNegObjAuto : subEqAddNegObj := by
  convexify

#print subEqAddNegObjAuto

-- sub_eq_add_neg (constr)
def subEqAddNegConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : y ≤ x + (-x)

-- sub_eq_add_neg-rev (obj)

-- sub_eq_add_neg-rev (constr)

-- -- add_sub (obj)
-- def addSubObj :=
--   optimization (x y : ℝ)
--     minimize (x + (x - y) : ℝ)
--     subject to
--       h : 0 ≤ x

-- time_cmd equivalence addSubObjRed/addSubObjAuto : addSubObj := by
--   convexify

-- #print addSubObjAuto

-- add_sub (constr)
def addSubConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h1 : 0 ≤ x
      h2 : x + (x - y) ≤ 1

time_cmd equivalence addSubConstrRed/addSubConstrAuto : addSubConstr := by
  convexify

#print addSubConstrAuto

-- add_sub-rev (obj)
def addSubRevObj :=
  optimization (x : ℝ)
    minimize ((1 + x) - x : ℝ)
    subject to
      h : 0 ≤ x

time_cmd equivalence addSubRevObjRed/addSubRevObjAuto : addSubRevObj := by
  convexify

#print addSubRevObjAuto

-- add_sub-rev (constr)
def addSubRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h1 : 0 ≤ x
      h2 : (1 + x) - x ≤ 1

time_cmd equivalence addSubRevConstrRed/addSubRevConstrAuto : addSubRevConstr := by
  convexify

#print addSubRevConstrAuto

-- add_mul (obj)
def addMulObj :=
  optimization (x y : ℝ)
    minimize ((-1 + sqrt x) * sqrt x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence addMulObjRed/addMulObjAuto : addMulObj := by
  convexify

-- add_mul (constr)
def addMulConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (-1 + sqrt x) * sqrt x ≤ 1

time_cmd equivalence addMulConstrRed/addMulConstrAuto : addMulConstr := by
  convexify

#print addMulConstrAuto

-- add_mul-rev (obj)
def addMulRevObj :=
  optimization (x : ℝ)
    minimize (2 * x + 3 * x : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence addMulRevObjRed/addMulRevObjAuto : addMulRevObj := by
  convexify

#print addMulRevObjAuto

-- add_mul-rev (constr)
def addMulRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      h : 2 * x + 3 * x ≤ 1

time_cmd equivalence addMulRevConstrRed/addMulRevConstrAuto : addMulRevConstr := by
  convexify

#print addMulRevConstrAuto

-- mul_add (obj)
def mulAddObj :=
  optimization (x : ℝ)
    minimize (sqrt x * (-1 + sqrt x) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulAddObjRed/mulAddObjAuto : mulAddObj := by
  convexify

#print mulAddObjAuto

-- mul_add (constr)
def mulAddConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : sqrt x * (-1 + sqrt x) ≤ 1

time_cmd equivalence mulAddConstrRed/mulAddConstrAuto : mulAddConstr := by
  convexify

#print mulAddConstrAuto

-- mul_add-rev (obj)
def mulAddRevObj :=
    optimization (x : ℝ)
    minimize (x * 2 + x * 3 : ℝ)
    subject to
      hx : 0 ≤ x
  
time_cmd equivalence mulAddRevObjRed/mulAddRevObjAuto : mulAddRevObj := by
  convexify

#print mulAddRevObjAuto

-- mul_add-rev (constr)
def mulAddRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      h : x * 2 + x * 3 ≤ 1

time_cmd equivalence mulAddRevConstrRed/mulAddRevConstrAuto : mulAddRevConstr := by
  convexify

#print mulAddRevConstrAuto

-- mul_sub (obj)
def mulSubObj :=
  optimization (x : ℝ)
    minimize (sqrt x * (sqrt x - 1) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulSubObjRed/mulSubObjAuto : mulSubObj := by
  convexify

#print mulSubObjAuto

-- mul_sub (constr)
def mulSubConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : sqrt x * (sqrt x - 1) ≤ 1

-- mul_sub-rev (obj)
def mulSubRevObj :=
  optimization (x : ℝ)
    minimize (x * 2 - x * 3 : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence mulSubRevObjRed/mulSubRevObjAuto : mulSubRevObj := by
  convexify

#print mulSubRevObjAuto

-- mul_sub-rev (constr)
def mulSubRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 ≤ x
      h : x * 2 - x * 3 ≤ 1

time_cmd equivalence mulSubRevConstrRed/mulSubRevConstrAuto : mulSubRevConstr := by
  convexify

#print mulSubRevConstrAuto

-- add_div (obj)
def addDivObj :=
  optimization (x y : ℝ)
    minimize ((exp x + 1) / (exp y) : ℝ)
    subject to
      hx : 0 ≤ x

time_cmd equivalence addDivObjRed/addDivObjAuto : addDivObj := by
  convexify

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
  convexify

#print addDivConstrAuto

-- add_div-rev (obj)
def addDivRevObj :=
  optimization (x : ℝ)
    minimize ((x / 2) + ((-x) / 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence addDivRevObjRed/addDivRevObjAuto : addDivRevObj := by
  convexify

-- add_div-rev (constr)
def addDivRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : (x / 2) + ((-x) / 2) ≤ x

time_cmd equivalence addDivRevConstrRed/addDivRevConstrAuto : addDivRevConstr := by
  convexify

#print addDivRevConstrAuto

-- mul_div (obj)
def mulDivObj :=
  optimization (x y : ℝ)
    minimize ((sqrt x) * (sqrt x / 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulDivObjRed/mulDivObjAuto : mulDivObj := by
  convexify

#print mulDivObjAuto

-- mul_div (constr)
def mulDivConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (sqrt x) * (sqrt x / 2) ≤ 1

time_cmd equivalence mulDivConstrRed/mulDivConstrAuto : mulDivConstr := by
  convexify

#print mulDivConstrAuto

-- mul_div-rev (obj)
def mulDivRevObj :=
  optimization (x y : ℝ)
    minimize ((x * y) / x : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence mulDivRevObjRed/mulDivRevObjAuto : mulDivRevObj := by
  convexify

#print mulDivRevObjAuto

-- mul_div-rev (constr)
def mulDivRevConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (x * y) / x ≤ 1

time_cmd equivalence mulDivRevConstrRed/mulDivRevConstrAuto : mulDivRevConstr := by
  convexify

#print mulDivRevConstrAuto

#check div_self

-- div_self (obj)
def divSelfObj :=
  optimization (x y : ℝ)
    minimize ((x / x) * y : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence divSelfObjRed/divSelfObjAuto : divSelfObj := by
  convexify

#print divSelfObjAuto

-- div_self (constr)
def divSelfConstr :=
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      hx : 0 < x
      h : (x / x) * y ≤ 1

time_cmd equivalence divSelfConstrRed/divSelfConstrAuto : divSelfConstr := by
  convexify
  
#print divSelfConstrAuto


/- Power and square root rules. -/

-- pow_add (obj)

-- pow_add (constr)

-- pow_add-rev (obj)

-- pow_add-rev (constr)

-- mul_pow (obj)

-- mul_pow (constr)

-- mul_pow-rev (obj)

-- mul_pow-rev (constr)

-- pow_mul (obj)

-- pow_mul (constr)

-- pow_mul-rev (obj)

-- pow_mul-rev (constr)

-- div_pow (obj)

-- div_pow (constr)

-- div_pow-rev (obj)

-- div_pow-rev (constr)

-- pow_sub (obj)

-- pow_sub (constr)

-- pow_sub-rev (obj)

-- pow_sub-rev (constr)

-- div_pow_eq_mul_pow_neg (obj)

-- div_pow_eq_mul_pow_neg (constr)

-- div_pow_eq_mul_pow_neg-rev (obj)

-- div_pow_eq_mul_pow_neg-rev (constr)

-- one_div_eq_pow_neg_one (obj)

-- one_div_eq_pow_neg_one (constr)

-- sqrt_eq_rpow (obj)

-- sqrt_eq_rpow (constr)

-- pow_half_two (obj)

-- pow_half_two (constr)


/- Exponential and logarithm rules. -/

-- exp_add (obj)
def expAddObj :=
  optimization (x y : ℝ)
    minimize (exp ((log x) + 2) : ℝ)
    subject to
      hx : 0 < x

time_cmd equivalence expAddObjRed/expAddObjAuto : expAddObj := by
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
  convexify

-- exp_add-rev (obj)

-- exp_add-rev (constr)

-- exp_sub (obj)

-- exp_sub (constr)

-- exp_sub-rev (obj)

-- exp_sub-rev (constr)

-- exp_mul (obj)

-- exp_mul (constr)

-- exp_mul-rev (obj)

-- exp_mul-rev (constr)

-- exp_neg_eq_one_div (obj)

-- exp_neg_eq_one_div (constr)

-- exp_neg_eq_one_div-rev (obj)
def expNegEqOneDivRevObj :=
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to
      h : 1 ≤ x

time_cmd equivalence expNegEqOneDivRevObjRed/expNegEqOneDivRevObjAuto : expNegEqOneDivRevObj := by
  convexify

#print expNegEqOneDivRevObjAuto

-- exp_neg_eq_one_div-rev (constr)
def expNegEqOneDivRevConstr :=
  optimization (x : ℝ)
    minimize (0 : ℝ)
    subject to
      h : 1 / (exp x) ≤ 1

-- log_mul (obj)

-- log_mul (constr)

-- log_mul-rev (obj)

-- log_mul-rev (constr)

-- log_div (obj)

-- log_div (constr)

-- log_div-rev (obj)

-- log_div-rev (constr)

-- exp_log (obj)

-- exp_log (constr)

-- log_exp (obj)

-- log_exp (constr)

end Rules