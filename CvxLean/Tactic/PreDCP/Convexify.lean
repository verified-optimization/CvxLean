import Lean
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

partial def CvxLean.Tree.and : List (Tree String String) → Tree String String
  | [] => Tree.leaf "true"
  | [t] => t
  | t1::t2::ts => Tree.node "and" #[t1, Tree.and (t2::ts)]

def CvxLean.Tree.ofOCTree (ocTree : OC (Tree String String)) :
  Tree String String :=
  let objFun := ocTree.objFun
  let constr := ocTree.constr
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constraints" #[Tree.and constr.data]
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
    ("constraints", ("constraints", 1, #[])),
    ("var",         ("var", 1, #[])),
    ("and",         ("and", 2, #[])),
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
        if children.size ≠ arity then
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
      let divisionRingToOfScientific :=
        mkApp2 (mkConst ``DivisionRing.toOfScientific ([levelZero] : List Level))
          (mkConst ``Real)
          (mkConst ``Real.instDivisionRingReal)
      let realOfScientific :=
        mkApp2 (mkConst ``OfScientific.ofScientific ([levelZero] : List Level))
          (mkConst ``Real)
          divisionRingToOfScientific
      let num := mkApp3 realOfScientific
        (mkNatLit res.mantissa.natAbs) (toExpr true) (mkNatLit res.exponent)
      if res.mantissa < 0 then
        return mkApp3 (mkConst ``Neg.neg ([levelZero] : List Level))
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
  -- And.
  | Tree.node "and" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkAnd t1 t2
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
      (mkConst ``Neg.neg ([levelZero] : List Level))
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
  | Tree.node "prob" #[Tree.node "objFun" #[objFun], Tree.node "constraints" #[constr]] => do
    let objFun ← treeToExpr (vars.map toString) objFun
    let constr ← treeToExpr (vars.map toString) constr

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

macro "iterative_conv_num " t:tactic : tactic => 
  `(tactic| internally_do (try { norm_num } <;> $t))

-- TODO(RFM): Not hard-coded.
-- The bool indicates whether they need solve an equality.
def findTactic (s : String) : MetaM (Bool × Syntax) := do
  match s with
  | "mul-exp" =>
    return (true, ← `(tactic| iterative_conv_num (rw [←Real.exp_add])))
  | "le-log" =>
    return (true, ← `(tactic| iterative_conv_num (rw [←Real.log_le_log] <;> positivity)))
  | "log-exp" =>
    return (true, ← `(tactic| iterative_conv_num (rw [Real.log_exp])))
  | "pow-exp" =>
    return (true, ← `(tactic| iterative_conv_num (rw [←Real.exp_mul])))
  | "div-exp" =>
    return (true, ← `(tactic| iterative_conv_num (rw [Real.exp_sub])))
  | "add-0-right" => 
    return (true, ← `(tactic| iterative_conv_num (ring)))
  | "sub-add" => 
    return (true, ← `(tactic| iterative_conv_num (ring)))
  | "div-add" => 
    return (true, ← `(tactic| iterative_conv_num (ring)))
  | "log-1" => 
    return (true, ← `(tactic| iterative_conv_num (rw [Real.log_one])))
  | "div-pow" => 
    return (true, ← `(tactic| iterative_conv_num (rw [div_eq_mul_inv, Real.rpow_neg] <;> positivity)))
  -- | "and-assoc" => 
  --   return (true, ← `(tactic| iterative_conv_num (rw [and_assoc])))
  | "mul-1-right" => 
    return (true, ← `(tactic| iterative_conv_num (ring)))
  | "sqrt_eq_rpow" => 
    return (true, ← `(tactic| iterative_conv_num (rw [Real.sqrt_eq_rpow])))
  | "le-div-one" => 
    return (true, ← `(tactic| iterative_conv_num (rw [←div_le_one] <;> norm_num; positivity)))
  | "map-objFun-log" =>
    return (false, ← `(tactic| map_objFun_log))
  | _ => throwError "Unknown rewrite name {s}."

elab "convexify" : tactic => withMainContext do
  let g ← getMainGoal

  -- NOTE(RFM): No whnf
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

    -- NOTE(RFM): No whnf
    let gTy := (← MVarId.getDecl g).type
    let gExpr ← Meta.matchSolutionExprFromExpr gTy

    let expectedTerm := step.expectedTerm
    let expectedSolutionExpr ← stringToSolutionExpr vars expectedTerm
    let expectedExpr := expectedSolutionExpr.toExpr
    let (needsEq, tac) ← findTactic step.rewriteName
    if needsEq then
      let eq ← mkEq expectedExpr gExpr.toExpr
      check eq
      let gs ← g.apply (← mkAppM `Eq.mp #[← mkFreshExprMVar eq])
      let gs1 ← evalTacticAt tac gs[1]!
      if gs1.length == 0 then
        replaceMainGoal gs
      else
        dbg_trace s!"Failed to rewrite {step.rewriteName}."
        replaceMainGoal gs
        break
    else
      let gs1 ← evalTacticAt tac g
      replaceMainGoal gs1

  return ()

open Minimization Real

set_option maxHeartbeats 1000000 in
lemma test : Solution (
    optimization (x y : ℝ)
      minimize (x * y)
      subject to
        hx : 0 < x
        hy : 0 < y
        h : x ^ 2 ≤ (10.123)
) := by
  map_exp
  convexify
  norm_num -- clean up numbers
  sorry
