import Lean
import Mathlib.Tactic.NormNum
import CvxLean.Tactic.Basic.RemoveConstr
import CvxLean.Tactic.DCP.Dcp
import CvxLean.Tactic.DCP.AtomLibrary
import CvxLean.Tactic.PreDCP.Basic
import CvxLean.Tactic.PreDCP.Sexp

open Lean Elab Meta Tactic Term IO
open CvxLean

section MinimizationToEgg

partial def CvxLean.Tree.toString : Tree String String → String
  | Tree.node n children =>
    let childrenStr := (children.map Tree.toString).data
    "(" ++ n ++ " " ++ (" ".intercalate childrenStr) ++ ")"
  | Tree.leaf n => n

def CvxLean.Tree.ofOCTree (ocTree : OC (Tree String String)) :
  Tree String String :=
  let objFun := ocTree.objFun
  let constr := ocTree.constr
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constraints" (Array.mk constr.data)
  Tree.node "prob" #[objFunNode, constrNode]

partial def CvxLean.Tree.surroundVars (t : Tree String String) (vars : List String) :=
  match t with
  | Tree.leaf s => if s ∈ vars then Tree.node "var" #[Tree.leaf s] else t
  | Tree.node n children => Tree.node n (children.map (surroundVars · vars))

-- TODO(RFM): Construct this map with commands, not hard-coded. For every key
-- we have the name, the arity and the extra args.
def Convexify.opMap : HashMap String (String × Nat × Array String) :=
  HashMap.ofList [
    ("prob",        ("prob", 2, #[])),
    ("objFun",      ("objFun", 1, #[])),
    ("constraints", ("constraints", 0, #[])),
    ("maximizeNeg", ("neg", 1, #[])),
    ("var",         ("var", 1, #[])),
    ("param",       ("param", 1, #[])),
    ("eq",          ("eq", 2, #[])),
    ("le",          ("le", 2, #[])),
    ("neg",         ("neg", 1, #[])),
    ("add",         ("add", 2, #[])),
    ("sub",         ("sub", 2, #[])),
    ("mul1",        ("mul", 2, #[])),
    ("mul2",        ("mul", 2, #[])),
    ("sq",          ("pow", 1, #["2"])),
    ("sqrt",        ("sqrt", 1, #[])),
    ("div",         ("div", 2, #[])),
    ("log",         ("log", 1, #[])),
    ("exp",         ("exp", 1, #[]))
  ]

partial def CvxLean.Tree.adjustOps (t : Tree String String) :
  MetaM (Tree String String) := do
  match t with
  | Tree.node op children =>
      if let some (op', arity, extraArgs) := Convexify.opMap.find? op then
        if children.size ≠ arity && op' != "constraints" then
          throwError s!"The operator {op} has arity {children.size}, but it should have arity {arity}."
        let children' ← children.mapM adjustOps
        let children' := children' ++ extraArgs.map Tree.leaf
        return Tree.node op' children'
      else
        throwError s!"The atom {op} is not supported by the `convexify` tactic."
  | Tree.leaf "unknown" => throwError "Unknown atom."
  | l => return l

def CvxLean.DCP.uncheckedTreeString (m : Meta.SolutionExpr) (vars : List String) :
  MetaM String := do
  let ocTree ← DCP.uncheckedTreeFromSolutionExpr m
  -- NOTE(RFM): Some empty constraints here coming from conditions?
  let ocTree := { ocTree with constr := ocTree.constr.filter (·.size > 1)}
  let tree := Tree.ofOCTree ocTree
  let tree := Tree.surroundVars tree vars
  let tree ← tree.adjustOps
  return tree.toString

end MinimizationToEgg

section EggToMinimization

partial def Sexpr.toTree : Sexp → MetaM (Tree String String)
  | .atom a => return Tree.leaf a
  | .list l => do
    if l.length == 0 then
      throwError "Sexp to Tree conversion error: unexpected empty list."
    else
      match l.head! with
      | .atom op =>
        let children ← l.tail.mapM toTree
        return CvxLean.Tree.node op (Array.mk children)
      | .list _ => throwError "Sexp to Tree conversion error: unexpected list as operator."

def CvxLean.stringToTree (s : String) : MetaM (Tree String String) := do
  match parseSingleSexp s with
  | Except.ok sexpr => Sexpr.toTree sexpr
  | Except.error e => throwError s!"{e}"

noncomputable instance Real.instDivReal : Div ℝ :=
  by infer_instance

partial def CvxLean.treeToExpr (vars : List String) : Tree String String → MetaM Expr
  -- Numbers.
  | Tree.leaf s =>
    match Json.Parser.num s.mkIterator with
    | Parsec.ParseResult.success _ res => do
      -- NOTE(RFM): This is not ideal, but it works if we use norm_num all the
      -- time.
      let divisionRingToOfScientific :=
        mkApp2 (mkConst ``DivisionRing.toOfScientific [levelZero])
          (mkConst ``Real)
          (mkConst ``Real.instDivisionRingReal)
      let realOfScientific :=
        mkApp2 (mkConst ``OfScientific.ofScientific [levelZero])
          (mkConst ``Real)
          divisionRingToOfScientific
      let num := mkApp3 realOfScientific
        (mkNatLit res.mantissa.natAbs) (toExpr true) (mkNatLit res.exponent)
      if res.mantissa < 0 then
        return mkApp3 (mkConst ``Neg.neg [levelZero])
          (mkConst ``Real) (mkConst ``Real.instNegReal) num
      else
        return num
    | _ => throwError "Tree to Expr conversion error: unexpected num {s}."
  -- Variables.
  | Tree.node "var" #[Tree.leaf s] =>
    if s ∈ vars then
      return mkFVar (FVarId.mk (Name.mkSimple s))
    else
      throwError "Tree to Expr conversion error: unexpected var {s}."
  -- Parameters.
  | Tree.node "param" #[Tree.leaf s] =>
    return mkConst (Name.mkSimple s)
  -- Equality.
  | Tree.node "eq" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    mkEq t1 t2
  -- Less than or equal to.
  | Tree.node "le" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkAppN
      (mkConst ``LE.le [levelZero])
      #[(mkConst `Real), (mkConst `Real.instLEReal), t1, t2]
  -- Negation.
  | Tree.node "neg" #[t] => do
    let t ← treeToExpr vars t
    return mkAppN
      (mkConst ``Neg.neg [levelZero])
      #[(mkConst ``Real), (mkConst ``Real.instNegReal), t]
  -- Square root. 
  | Tree.node "sqrt" #[t] => do
    let t ← treeToExpr vars t
    return mkAppN (mkConst ``Real.sqrt) #[t]
  -- Addition.
  | Tree.node "add" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkRealHBinAppExpr ``HAdd.hAdd ``instHAdd 1 ``Real.instAddReal t1 t2
  -- Subtraction.
  | Tree.node "sub" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkRealHBinAppExpr ``HSub.hSub ``instHSub 1 ``Real.instSubReal t1 t2
  -- Multiplication.
  | Tree.node "mul" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkRealHBinAppExpr ``HMul.hMul ``instHMul 1 ``Real.instMulReal t1 t2
  -- Division.
  | Tree.node "div" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkRealHBinAppExpr ``HDiv.hDiv ``instHDiv 1 ``Real.instDivReal t1 t2
  -- Log.
  | Tree.node "log" #[t] => do
    let t ← treeToExpr vars t
    return mkAppN (mkConst ``Real.log) #[t]
  -- Exp.
  | Tree.node "exp" #[t] => do
    let t ← treeToExpr vars t
    return mkAppN (mkConst ``Real.exp) #[t]
  -- Pow.
  | Tree.node "pow" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkRealHBinAppExpr ``HPow.hPow ``instHPow 2 ``Real.instPowReal t1 t2
  -- Error.
  | Tree.node op children =>
    throwError "Tree to Expr conversion error: unexpected op {op} with {children.size} children."
where
  mkRealHBinAppExpr (opName instHName : Name) (nTyArgs : Nat) (instName : Name)
    (e1 e2 : Expr) : Expr :=
    let R := Lean.mkConst ``Real
    let inst := mkAppN (mkConst instHName (List.replicate nTyArgs levelZero))
      (Array.mk (List.replicate nTyArgs R) ++ [Lean.mkConst instName])
    mkAppN
      (mkConst opName [levelZero, levelZero, levelZero])
      #[R, R, R, inst, e1, e2]

def CvxLean.treeToSolutionExpr (vars : List Name) (t : Tree String String) :
  MetaM (Option Meta.SolutionExpr) := do
  match t with
  | Tree.node "prob" #[Tree.node "objFun" #[objFun], Tree.node "constraints" constr] => do
    let objFun ← treeToExpr (vars.map toString) objFun
    let constr ← constr.mapM <| treeToExpr (vars.map toString)
    let constr := Meta.composeAnd constr.data

    -- NOTE(RFM): Assuming all variables are real.
    let fvars := Array.mk $ vars.map (fun v => mkFVar (FVarId.mk v))
    let vars := vars.map (fun v => (v, Lean.mkConst ``Real))
    let domain := Meta.composeDomain vars
    withLocalDeclD `p domain fun p => do
      Meta.withDomainLocalDecls domain p fun xs prs => do
        let objFun := Expr.replaceFVars objFun fvars xs
        let objFun ← mkLambdaFVars #[p] $ Expr.replaceFVars objFun xs prs
        let constraints := Expr.replaceFVars constr fvars xs
        let constraints ← mkLambdaFVars #[p] $ Expr.replaceFVars constraints xs prs
        return some {
          domain := domain,
          codomain := mkConst ``Real,
          codomainPreorder := mkConst ``Real.instPreorderReal,
          domain' := domain,
          codomain' := mkConst ``Real,
          objFun := objFun,
          constraints := constraints
        }
  | _ => throwError "Tree to SolutionExpr conversion error: unexpected tree structure."

def CvxLean.stringToSolutionExpr (vars : List Name) (s : String) :
  MetaM (Meta.SolutionExpr) := do
  let t ← stringToTree s
  match ← treeToSolutionExpr vars t with
  | some se => return se
  | none => throwError "String to SolutionExpr conversion error."

end EggToMinimization

-- Taken from https://github.com/opencompl/egg-tactic-code

def Lean.Json.getStr! (j : Json) : String :=
  match j with
  | Json.str a => a
  | _ => ""

def Lean.Json.getArr! (j : Json) : Array Json :=
  match j with
  | Json.arr a => a
  | _ => #[]

def MetaM.ofExcept [ToString ε]: Except ε α -> MetaM α :=
  fun e =>
    match e with
    | Except.error msg => throwError (toString msg)
    | Except.ok x => return x

instance : MonadExceptOf String MetaM := {
  throw := fun msg => throwError msg
  tryCatch := fun x _ => x
}

def surroundQuotes (s : String) : String :=
  "\"" ++ s ++ "\""

structure EggRequest where
  target : String

def EggRequest.toJson (e : EggRequest) : String := "{"
  ++ surroundQuotes "request" ++ ":"
  ++ surroundQuotes "PerformRewrite" ++ ","
  ++ surroundQuotes "target" ++ ":" ++ (surroundQuotes e.target)
  ++ "}"

inductive EggRewriteDirection where
  | Forward
  | Backward
  deriving Inhabited, DecidableEq

def EggRewriteDirection.toString : EggRewriteDirection → String
  | Forward => "fwd"
  | Backward => "bwd"

instance : ToString EggRewriteDirection where
  toString := EggRewriteDirection.toString

structure EggRewrite where
  rewriteName : String
  direction : EggRewriteDirection
  expectedTerm : String

def EggRewrite.toString (e : EggRewrite) : String := "{"
  ++ surroundQuotes "rewrite_name" ++ ":" ++ surroundQuotes e.rewriteName ++ ","
  ++ surroundQuotes "direction" ++ ":" ++ surroundQuotes (e.direction.toString) ++ ","
  ++ surroundQuotes "expected_term" ++ ":" ++ surroundQuotes e.expectedTerm
  ++ "}"

instance : ToString EggRewrite where
  toString := EggRewrite.toString

def runEggRequestRaw (requestJson : String) : MetaM String := do
    let eggProcess ← IO.Process.spawn {
        cmd    := "rewriter/utils/egg-convexify",
        stdout := IO.Process.Stdio.piped,
        stdin  := IO.Process.Stdio.piped,
        stderr := IO.Process.Stdio.null
      }

    let (stdin, eggProcess) ← eggProcess.takeStdin
    stdin.putStr requestJson

    let stdout ← IO.asTask eggProcess.stdout.readToEnd Task.Priority.dedicated
    let stdout : String ← IO.ofExcept stdout.get
    let exitCode ← eggProcess.wait
    dbg_trace s!"Egg exit code: {exitCode}"

    return stdout

def parseEggResponse (responseString : String) : MetaM (Array EggRewrite) := do
  dbg_trace s!"Egg response: {responseString}"
  let outJson : Json ← match Json.parse responseString with
    | Except.error e => throwError "JSON parsing error: {e} at {responseString}."
    | Except.ok j => pure j

  let responseType := (outJson.getObjValD "response").getStr!

  if responseType == "error" then
    throwError "Error calling egg."
  else
    let steps ← liftExcept <| outJson.getObjVal? "steps"
    let steps ← liftExcept <| Json.getArr? steps

    let res := steps.map fun step =>
      let rewriteName := (step.getObjValD "rewrite_name").getStr!
      let direction := match (step.getObjValD "direction").getStr! with
        | "Forward" => EggRewriteDirection.Forward
        | "Backward" => EggRewriteDirection.Backward
        | _ => panic! "Unexpected rewrite direction."
      let expectedTerm := (step.getObjValD "expected_term").getStr!
      { rewriteName  := rewriteName,
        direction    := direction,
        expectedTerm := expectedTerm }

    return res

def runEggRequest (request : EggRequest) : MetaM (Array EggRewrite) :=
  dbg_trace s!"Running egg request: {request.toJson}"
  runEggRequestRaw request.toJson >>= parseEggResponse

macro "posimptivity" : tactic => 
  `(tactic| norm_num <;> positivity)

lemma and_eq_and {A B C D : Prop} (h1 : A = C) (h2 : B = D) : (A ∧ B) = (C ∧ D):= by
  congr

-- TODO(RFM): Do I need this? Can I just use congr?
macro "split_ands" : tactic => 
  `(tactic| repeat (apply and_eq_and ; try { rfl }))

theorem Real.log_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x = Real.log y ↔ x = y :=
  ⟨fun h => by { 
    have hxmem := Set.mem_Ioi.2 hx
    have hymem := Set.mem_Ioi.2 hy
    have heq : Set.restrict (Set.Ioi 0) log ⟨x, hxmem⟩ = 
      Set.restrict (Set.Ioi 0) log ⟨y, hymem⟩ := by 
      simp [h]
    have h := Real.log_injOn_pos.injective heq
    simp [Subtype.eq] at h
    exact h
  }, fun h => by rw [h]⟩

-- TODO(RFM): Use this lemma instead of exp_neg.
lemma Real.exp_neg2 : ∀ x : ℝ, exp (-x) = 1 / exp x := by
  intro x
  rw [Real.exp_neg, inv_eq_one_div]

-- TODO(RFM): Not hard-coded.
-- NOTE(RFM): The bool indicates whether they need solve an equality.
def findTactic : String → EggRewriteDirection →  MetaM (Bool × Syntax)
  | "inv-exp", _ => 
    return (true, ← `(tactic| simp only [Real.exp_neg2] <;> norm_num))
  | "mul-exp", _ => 
    return (true, ← `(tactic| simp only [←Real.exp_add] <;> norm_num))
  | "le-log", EggRewriteDirection.Forward =>
    return (true, ← `(tactic| try { conv in (Real.log _ ≤ Real.log _) => rw [Real.log_le_log (by posimptivity) (by posimptivity)] }))
  | "le-sub", EggRewriteDirection.Forward =>
    return (true, ← `(tactic| simp only [le_sub_iff_add_le] <;> norm_num))
  -- TODO(RFM): This is buggy.
  | "le-mul-rev", _ => 
    return (true, ← `(tactic| congr <;> funext <;> split_ands <;> try { rw [div_le_iff (by positivity)] <;> norm_num }))
  | "eq-log", EggRewriteDirection.Forward =>
    return (true, ← `(tactic| try { conv in (Real.log _ = Real.log _) => rw [Real.log_eq_log (by posimptivity) (by posimptivity)] }))
  | "log-exp", _ =>
    return (true, ← `(tactic| simp only [Real.log_exp]))
  | "log-div", EggRewriteDirection.Forward => 
    return (true, ← `(tactic| congr <;> funext <;> split_ands <;> try { rw [Real.log_div (by positivity) (by positivity)] <;> norm_num }))
  | "log-mul", _ => 
    return (true, ← `(tactic| congr <;> funext <;> split_ands <;> try { rw [Real.log_mul (by positivity) (by positivity)] <;> norm_num }))
  | "pow-exp", _ =>
    return (true, ← `(tactic| simp only [←Real.exp_mul] <;> norm_num))
  | "div-exp", _ =>
    return (true, ← `(tactic| simp only [←Real.exp_sub] <;> norm_num))
  | "add-assoc", _ => 
    return (true, ← `(tactic| simp only [add_assoc] <;> norm_num))
  | "add-mul", _ => 
    return (true, ← `(tactic| simp only [add_mul] <;> norm_num))
  | "add-sub", _ => 
    return (true, ← `(tactic| simp only [add_sub] <;> norm_num))
  | "div-add", _ => 
    return (true, ← `(tactic| simp only [add_div] <;> norm_num))
  | "sub-mul-left", _ => 
    return (true, ← `(tactic| simp only [←mul_sub] <;> norm_num))
  | "div-pow", _ => 
    return (true, ← `(tactic| try { conv in (_ / (_ ^  _)) => rw [div_eq_mul_inv, ←Real.rpow_neg (by posimptivity)] }))
  | "mul-comm", _ => 
    return (true, ← `(tactic| simp only [mul_comm] <;> norm_num))
  | "mul-assoc", _ => 
    return (true, ← `(tactic| simp only [mul_assoc] <;> norm_num))
  | "mul-add", _ => 
    return (true, ← `(tactic| simp only [mul_add] <;> norm_num))
  | "add-comm", _ => 
    return (true, ← `(tactic| simp only [add_comm] <;> norm_num))
  | "mul-div", _ => 
    return (true, ← `(tactic| simp only [mul_div] <;> norm_num))
  | "div-mul", _ => 
    return (true, ← `(tactic| simp only [←mul_div] <;> norm_num))
  | "sqrt_eq_rpow", _ => 
    return (true, ← `(tactic| simp only [Real.sqrt_eq_rpow] <;> norm_num))
  | "le-div-one", EggRewriteDirection.Forward => 
    return (true, ← `(tactic| congr <;> funext <;> split_ands <;> try { rw [←div_le_one (by posimptivity)]; norm_num } <;> norm_num))
  -- NOTE(RFM): Only instance of a rewriting without proving equality.
  | "map-objFun-log", EggRewriteDirection.Forward =>
    return (false, ← `(tactic| map_objFun_log))
  | rewriteName, direction => 
    throwError "Unknown rewrite name {rewriteName}({direction})."

-- Used to get rid of the `OfScientific`s.
def norm_num_clean_up (useSimp : Bool) : TacticM Unit :=
  Mathlib.Meta.NormNum.elabNormNum mkNullNode mkNullNode (useSimp := useSimp)

elab "convexify" : tactic => withMainContext do
  norm_num_clean_up (useSimp := false)

  let g ← getMainGoal
  
  -- NOTE(RFM): No whnf.              
  let gTy := (← MVarId.getDecl g).type
  let gExpr ← Meta.matchSolutionExprFromExpr gTy

  let vars ← withLambdaBody gExpr.constraints fun p _ => do
    let pr ← Meta.mkProjections gExpr.domain p
    return pr.map (Prod.fst)
  let varsStr := vars.map toString

  let gStr ← DCP.uncheckedTreeString gExpr varsStr

  let eggRequest := {
    target := gStr
  }
  let steps := ← runEggRequest eggRequest

  for step in steps do
    let g ← getMainGoal

    -- NOTE(RFM): No whnf.
    let gTy := (← MVarId.getDecl g).type
    let gExpr ← Meta.matchSolutionExprFromExpr gTy

    let expectedTerm := step.expectedTerm
    let expectedSolutionExpr ← stringToSolutionExpr vars expectedTerm
    let expectedExpr := expectedSolutionExpr.toExpr
    let (needsEq, tac) ← findTactic step.rewriteName step.direction
    if needsEq then
      let eq ← mkEq gExpr.toExpr expectedExpr
      let gs ← g.apply (← mkAppM `Eq.mpr #[← mkFreshExprMVar eq])
      let gs1 ← evalTacticAt tac gs[1]!
      if gs1.length == 0 then
        dbg_trace s!"Rewrote {step.rewriteName}."
        replaceMainGoal gs
      else
        dbg_trace s!"Failed to rewrite {step.rewriteName}."
        replaceMainGoal (gs ++ gs1)
        break
    else
      dbg_trace s!"Rewrote {step.rewriteName}."
      let gs1 ← evalTacticAt tac g
      replaceMainGoal gs1

  norm_num_clean_up (useSimp := true)

  return ()
