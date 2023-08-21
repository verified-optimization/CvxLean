import Lean
import Mathlib.Tactic.NormNum
import CvxLean.Tactic.Basic.RemoveConstr
import CvxLean.Tactic.PreDCP.UncheckedDCP
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

def CvxLean.Tree.ofOCTree (ocTree : OC (String × Tree String String)) :
  Tree String String :=
  let objFun := ocTree.objFun.2
  let constrs := ocTree.constr.map 
    fun (h, c) => Tree.node "constr" #[Tree.leaf h, c]
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constrs" constrs
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
    ("constr",      ("constr", 2, #[])),
    ("constrs",     ("constrs", 0, #[])),
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
        if children.size ≠ arity && op' != "constrs" then
          throwError s!"The operator {op} has arity {children.size}, but it should have arity {arity}."
        let children' ← children.mapM adjustOps
        let children' := children' ++ extraArgs.map Tree.leaf
        return Tree.node op' children'
      else
        throwError s!"The atom {op} is not supported by the `convexify` tactic."
  | Tree.leaf "unknown" => throwError "Unknown atom."
  | l => return l

def CvxLean.uncheckedTreeString (m : Meta.SolutionExpr) (vars : List String) :
  MetaM (OC (String × Tree String String) × Array String) := do
  let ocTree ← UncheckedDCP.uncheckedTreeFromSolutionExpr m
  -- Detect domain constraints of the form 0 <= x.
  -- NOTE(RFM): Assume there are no '<' constraints.
  let nonnegVars := ocTree.constr.filterMap <| fun (_, c) =>
    match c with
    | Tree.node "le" #[Tree.leaf "0", Tree.leaf v] => 
        if v ∈ vars then some v else none 
    | _ => none

  -- NOTE(RFM): Some empty constraints here coming from '<' conditions?
  let ocTree := { ocTree with 
    constr := ocTree.constr.filter (fun (h, c) => c.size > 1)}

  -- TODO(RFM): Functions for this.
  let ocTree : OC (String × Tree String String) := { 
    objFun := let (ho, o) := ocTree.objFun; (ho, Tree.surroundVars o vars)
    constr := ocTree.constr.map (fun (h, c) => (h, Tree.surroundVars c vars)) }
  let ocTree : OC (String × Tree String String) := {
    objFun := (ocTree.objFun.1, ← Tree.adjustOps ocTree.objFun.2)
    constr := ← ocTree.constr.mapM (fun (h, c) => return (h, ← Tree.adjustOps c)) }
  return (ocTree, nonnegVars)

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
  -- Constr.
  | Tree.node "constr" #[Tree.leaf s, t] => do
    let t ← treeToExpr vars t
    return Meta.mkLabel (Name.mkSimple s) t
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

-- TODO(RFM): Rename.
def CvxLean.stringToExpr (vars : List Name) (s : String) : MetaM Expr :=
  stringToTree s >>= treeToExpr (vars.map toString)

-- TODO(RFM): Rename.
def CvxLean.treeToSolutionExpr (vars : List Name) (t : Tree String String) :
  MetaM (Option Meta.SolutionExpr) := do
  match t with
  | Tree.node "prob" #[Tree.node "objFun" #[objFun], Tree.node "constrs" constr] => do
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
  | _ => throwError "Tree to SolutionExpr conversion error: unexpected tree structure {t}."

-- TODO(RFM): Rename.
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

structure EggMinimization where 
  objFun : String 
  constrs : List (List String) -- Tuples are lists of two elements.

def EggMinimization.toJson (e : EggMinimization) : String := 
  "{" ++ 
  surroundQuotes "obj_fun" ++ " : " ++ surroundQuotes e.objFun ++ ", " ++
  surroundQuotes "constrs" ++ " : " ++ 
    "[" ++
      (", ".intercalate <| e.constrs.map (fun d => 
        "[" ++ ",".intercalate (d.map surroundQuotes) ++ "]")) ++
    "]" ++
  "}"

def EggMinimization.ofOCTree (oc : OC (String × Tree String String)) : EggMinimization :=
  { objFun := oc.objFun.2.toString, 
    constrs := Array.data <| oc.constr.map fun (h, c) => [h, c.toString] }

structure EggRequest where
  domains : List (List String) -- Tuples are lists of two elements.
  target : EggMinimization

def EggRequest.toJson (e : EggRequest) : String := 
  "{" ++ 
  surroundQuotes "request" ++ " : " ++ surroundQuotes "PerformRewrite" ++ ", " ++ 
  surroundQuotes "domains" ++ " : " ++ 
    "[" ++
      (", ".intercalate <| e.domains.map (fun d => 
        "[" ++ ",".intercalate (d.map surroundQuotes) ++ "]")) ++
    "]" ++ ", " ++
  surroundQuotes "target" ++ " : " ++ (e.target.toJson) ++ 
  "}"

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
  location : String
  expectedTerm : String

def EggRewrite.toString (e : EggRewrite) : String := "{"
  ++ surroundQuotes "rewrite_name" ++ ":" ++ surroundQuotes e.rewriteName ++ ","
  ++ surroundQuotes "direction" ++ ":" ++ surroundQuotes (e.direction.toString) ++ ","
  ++ surroundQuotes "location" ++ ":" ++ surroundQuotes e.location ++ ","
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
      let location := (step.getObjValD "location").getStr!
      let expectedTerm := (step.getObjValD "expected_term").getStr!
      { rewriteName  := rewriteName,
        direction    := direction,
        location     := location,
        expectedTerm := expectedTerm }

    return res

def runEggRequest (request : EggRequest) : MetaM (Array EggRewrite) :=
  dbg_trace s!"Running egg request: {request.toJson}"
  runEggRequestRaw request.toJson >>= parseEggResponse

macro "posimptivity" : tactic => 
  `(tactic| norm_num <;> positivity)

-- TODO(RFM): Move.
lemma Real.log_eq_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : Real.log x = Real.log y ↔ x = y :=
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

-- TODO(RFM): Move.
lemma Real.div_pow_eq_mul_pow_neg {a b c : ℝ} (hb : 0 ≤ b) : a / (b ^ c) = a * b ^ (-c) := by
  rw [div_eq_mul_inv, ←Real.rpow_neg hb]

-- TODO(RFM): Move.
lemma Real.exp_neg_eq_one_div (x : ℝ) : exp (-x) = 1 / exp x := by
  rw [Real.exp_neg, inv_eq_one_div]

-- TODO(RFM): Not hard-coded.
-- NOTE(RFM): The bool indicates whether they need solve an equality.
def findTactic : String → EggRewriteDirection → Bool × MetaM (TSyntax `tactic)
  
  /- Objective function rules. -/
  -- NOTE(RFM): Only instance of a rewriting without proving equality.
  | "map_objFun_log", EggRewriteDirection.Forward =>
    (false, `(tactic| map_objFun_log))
  
  /- Equality rules. -/
  | "log_eq_log", EggRewriteDirection.Forward =>
    -- NOTE(RFM): This was conv in (Real.log _ = Real.log _).
    (true, `(tactic| simp only [Real.log_eq_log (by posimptivity) (by posimptivity)]))
  
  /- Less than or equal rules. -/
  | "le_sub_iff_add_le", EggRewriteDirection.Forward =>
    (true, `(tactic| simp only [le_sub_iff_add_le]))
  | "div_le_iff", _ => 
    -- NOTE(RFM): This was rw.
    (true, `(tactic| simp only [div_le_iff (by positivity)]))
  | "div_le_one-rev", EggRewriteDirection.Forward => 
    (true, `(tactic| simp only [←div_le_one (by posimptivity)]))
  | "log_le_log", EggRewriteDirection.Forward =>
    -- NOTE(RFM): This was conv in (Real.log _ ≤ Real.log _).
    (true, `(tactic| simp only [Real.log_le_log (by posimptivity) (by posimptivity)]))
  
  /- Field rules. -/
  | "add_comm", _ => 
    (true, `(tactic| simp only [add_comm]))
  | "add_assoc", _ => 
    (true, `(tactic| simp only [add_assoc]))
  | "mul_comm", _ => 
    (true, `(tactic| simp only [mul_comm]))
  | "mul_assoc", _ => 
    (true, `(tactic| simp only [mul_assoc]))
  | "add_sub", _ => 
    (true, `(tactic| simp only [add_sub]))
  | "add_mul", _ => 
    (true, `(tactic| simp only [add_mul]))
  | "mul_add", _ => 
    (true, `(tactic| simp only [mul_add]))
  | "mul_sub-rev", _ => 
    (true, `(tactic| simp only [←mul_sub]))
  | "add_div", _ => 
    (true, `(tactic| simp only [add_div]))
  | "mul_div", _ => 
    (true, `(tactic| simp only [mul_div]))
  | "mul_div-rev", _ => 
    (true, `(tactic| simp only [←mul_div]))

  /- Power and square root rules. -/
  | "div_pow_eq_mul_pow_neg", _ => 
    -- NOTE(RFM): This was conv in (_ / (_ ^  _)).
    (true, `(tactic| simp only [Real.div_pow_eq_mul_pow_neg (by posimptivity)]))
  | "sqrt_eq_rpow", _ => 
    (true, `(tactic| simp only [Real.sqrt_eq_rpow]))
  
  /- Exponential and logarithm rules. -/
  | "exp_add", _ =>
    (true, `(tactic| simp only [Real.exp_add]))
  | "exp_add-rev", _ =>
    (true, `(tactic| simp only [←Real.exp_add]))
  | "exp_sub", _ =>
    (true, `(tactic| simp only [Real.exp_sub]))
  | "exp_sub-rev", _ =>
    (true, `(tactic| simp only [←Real.exp_sub]))
  | "exp_mul", _ =>
    (true, `(tactic| simp only [Real.exp_mul]))
  | "exp_mul-rev", _ =>
    (true, `(tactic| simp only [←Real.exp_mul]))
  | "exp_neg_eq_one_div-rev", _ =>
    (true, `(tactic| simp only [←Real.exp_neg_eq_one_div]))
  | "log_mul", _ => 
    (true, `(tactic| simp only [Real.log_mul (by positivity) (by positivity)]))
  | "log_div", _ => 
    (true, `(tactic| simp only [Real.log_div (by positivity) (by positivity)]))
  | "log_exp", _ =>
    (true, `(tactic| simp only [Real.log_exp]))

  /- Unknown rule. -/
  | rewriteName, direction => 
    (false, throwError "Unknown rewrite name {rewriteName}({direction}).")


/-- Given the rewrite index (`0` for objective function, `1` to `numConstr` for 
for for constraints), return the rewrite lemma that needs to be applied. Also 
return the number of arguments of each rewrite lemma to be able to build an 
expression in `rewriteWrapperApplyExpr`. -/
def rewriteWrapperLemma (rwIdx : Nat) (numConstrs : Nat) : MetaM (Name × Nat) := 
  if rwIdx == 0 then 
    return (`Minimization.rewrite_objective, 1)
  else if numConstrs == 1 then 
    -- Rewriting a single constraint is the same as rewriting all constraints.
    return (`Minimization.rewrite_constraints, 1)
  else if rwIdx == numConstrs then 
    match rwIdx with 
    | 1  => return (`Minimization.rewrite_constraint_1_last,  1)
    | 2  => return (`Minimization.rewrite_constraint_2_last,  2)
    | 3  => return (`Minimization.rewrite_constraint_3_last,  3)
    | 4  => return (`Minimization.rewrite_constraint_4_last,  4)
    | 5  => return (`Minimization.rewrite_constraint_5_last,  5)
    | 6  => return (`Minimization.rewrite_constraint_6_last,  6)
    | 7  => return (`Minimization.rewrite_constraint_7_last,  7)
    | 8  => return (`Minimization.rewrite_constraint_8_last,  8)
    | 9  => return (`Minimization.rewrite_constraint_9_last,  9)
    | 10 => return (`Minimization.rewrite_constraint_10_last, 10)
    | _  => throwError "convexify can only rewrite problems with up to 10 constraints."
  else
    match rwIdx with 
    | 1  => return (`Minimization.rewrite_constraint_1,  1)
    | 2  => return (`Minimization.rewrite_constraint_2,  2)
    | 3  => return (`Minimization.rewrite_constraint_3,  3)
    | 4  => return (`Minimization.rewrite_constraint_4,  4)
    | 5  => return (`Minimization.rewrite_constraint_5,  5)
    | 6  => return (`Minimization.rewrite_constraint_6,  6)
    | 7  => return (`Minimization.rewrite_constraint_7,  7)
    | 8  => return (`Minimization.rewrite_constraint_8,  8)
    | 9  => return (`Minimization.rewrite_constraint_9,  9)
    | 10 => return (`Minimization.rewrite_constraint_10, 10)
    | _  => throwError "convexify can only rewrite problems with up to 10 constraints."

def rewriteWrapperApplyExpr (rwName : Name) (numArgs : Nat) (expected : Expr) : 
  MetaM Expr := do
  let signature := #[← mkFreshExprMVar none, Lean.mkConst `Real, ← mkFreshExprMVar none]
  let args ← Array.range numArgs |>.mapM fun _ => mkFreshExprMVar none
  return mkAppN (mkConst rwName) (signature ++ args ++ #[expected])

-- Used to get rid of the `OfScientific`s.
def norm_num_clean_up (useSimp : Bool) : TacticM Unit :=
  Mathlib.Meta.NormNum.elabNormNum mkNullNode mkNullNode (useSimp := useSimp)

elab "convexify" : tactic => withMainContext do
  norm_num_clean_up (useSimp := false)

  let g ← getMainGoal
  
  -- NOTE(RFM): No whnf.              
  let gTy := (← MVarId.getDecl g).type
  let gExpr ← Meta.matchSolutionExprFromExpr gTy

  -- Get optimization variables.
  let vars ← withLambdaBody gExpr.constraints fun p _ => do
    let pr ← Meta.mkProjections gExpr.domain p
    return pr.map (Prod.fst)
  let varsStr := vars.map toString
  let fvars := Array.mk $ vars.map (fun v => mkFVar (FVarId.mk v))
  let domain := Meta.composeDomain <| vars.map (fun v => (v, Lean.mkConst ``Real))

  -- Get goal as tree and tags.
  let (gStr, nonnegVars) ← uncheckedTreeString gExpr varsStr
  let numConstrTags := gStr.constr.size
  let mut tagsMap := HashMap.empty
  tagsMap := tagsMap.insert "objFun" 0 
  let mut idx := 1
  for (h, _) in gStr.constr do
    tagsMap := tagsMap.insert h idx 
    idx := idx + 1

  -- Call egg.
  let eggRequest := {
    domains := Array.data <| nonnegVars.map (fun v => [v, "NonNeg"]),
    target := EggMinimization.ofOCTree gStr
  }
  let steps ← runEggRequest eggRequest

  for step in steps do
    let g ← getMainGoal

    let tag := step.location
    let tagNum := tagsMap.find! tag
    let (rwWrapper, numIntros) ← rewriteWrapperLemma tagNum numConstrTags
    dbg_trace s!"Rewriting {step.rewriteName} at {tag} ({tagNum}). {rwWrapper}."

    let expectedTermStr := step.expectedTerm
    let mut expectedExpr ← stringToExpr vars expectedTermStr
    if tagNum > 0 then 
      expectedExpr := Meta.mkLabel (Name.mkSimple tag) expectedExpr
    expectedExpr ← withLocalDeclD `p domain fun p => do
      Meta.withDomainLocalDecls domain p fun xs prs => do
        let replacedFVars := Expr.replaceFVars expectedExpr fvars xs
        mkLambdaFVars #[p] $ Expr.replaceFVars replacedFVars xs prs

    let (needsEq, tac) := findTactic step.rewriteName step.direction
    let tacStx ← tac
    if needsEq then
      let gs ← g.apply (← rewriteWrapperApplyExpr rwWrapper numIntros expectedExpr)

      if gs.length != 2 then 
        dbg_trace s!"Failed to rewrite {step.rewriteName}."
        replaceMainGoal gs; break

      let gToRw := gs[0]!
      let gToRwTag ← gToRw.getTag

      if gToRwTag != `hrw then 
        dbg_trace s!"Unexpected tag name {gToRwTag} when rewriting {step.rewriteName}."
        replaceMainGoal gs; break
      
      let gSol := gs[1]!
      let gSolTag ← gSol.getTag

      if gSolTag != `sol then
        dbg_trace s!"Unexpected tag name {gSolTag} when rewriting {step.rewriteName}."
        replaceMainGoal gs; break

      gSol.setTag Name.anonymous

      let fullTac : Syntax ← `(tactic| intros; $tacStx <;> norm_num)
      let gsAfterRw ← evalTacticAt fullTac gToRw

      -- let eq ← mkEq gExpr.toExpr expectedExpr
      -- let gs ← g.apply (← mkAppM `Eq.mpr #[← mkFreshExprMVar eq])
      -- let gs1 ← evalTacticAt tac gs[1]!
      if gsAfterRw.length == 0 then
        dbg_trace s!"Rewrote {step.rewriteName}."
        replaceMainGoal [gSol]
      else
        dbg_trace s!"Failed to rewrite {step.rewriteName}."
        replaceMainGoal (gs ++ gsAfterRw); break
    else
      let gs ← evalTacticAt tacStx g
      dbg_trace s!"Rewrote {step.rewriteName}."
      replaceMainGoal gs

  norm_num_clean_up (useSimp := false)

  return ()
