import CvxLean.Command.Solve
import CvxLean.Tactic.PreDCP.Convexify
import CvxLean.Tactic.Conv.ConvOpt

-- TODO(RFM): Move.
syntax (name := time_cmd) "time_cmd " command : command

@[command_elab «time_cmd»]
def evalTimeCmd : Lean.Elab.Command.CommandElab := fun stx => match stx with
| `(time_cmd $cmd) => do
  let before ← BaseIO.toIO IO.monoMsNow
  Lean.Elab.Command.elabCommand cmd
  let after ← BaseIO.toIO IO.monoMsNow
  let diff := after - before
  IO.println s!"{diff} ms"
| _ => Lean.Elab.throwUnsupportedSyntax

noncomputable section Rules

open CvxLean Minimization Real

def invExpObj := 
  optimization (x : ℝ)
    minimize (1 / (exp x))
    subject to 
      h : 1 ≤ x

time_cmd reduction invExpObjRedAuto/invExpObjAuto : invExpObj := by
  unfold invExpObj
  convexify
  exact done

-- time_cmd reduction invExpObjRedManual/invExpObjManual : invExpObj := by
--   unfold invExpObj
--   map_objFun_log
--   apply rewrite_objective
--     (f := fun x => log (1 / exp x)) 
--     (g := fun x => (log (exp (-x)))) 
--     (hfg := fun x _ => by simp only [←Real.exp_neg2])
--   -- simp only [←Real.exp_neg2]
--   simp only [Real.log_exp]

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

def logLeLogConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to 
      h : log x ≤ log y

-- NOTE(RFM): Why does it apply the rewrite?
#check le_sub_iff_add_le
def leSubConstr := 
  optimization (x y : ℝ)
    minimize (0 : ℝ)
    subject to
      h : x ≤ 1 - x

reduction leSubConstrRedAuto/leSubConstrAuto : leSubConstr := by 
  unfold leSubConstr
  convexify

def leMulRevConstr := False

def eqLogConstr := False

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