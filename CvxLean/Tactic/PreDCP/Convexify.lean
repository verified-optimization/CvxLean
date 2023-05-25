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
  | t1::t2::ts => Tree.and ((Tree.node "and" #[t1, t2])::ts)

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

-- TODO(RFM): Construct this map with commands, not hard-coded.
def Convexify.opMap : HashMap String String := HashMap.ofList [
  ("prob",        "prob"),
  ("objFun",      "objFun"),
  ("constraints", "constraints"),
  ("var",         "var"),
  ("and",         "and"),
  ("eq",          "eq"),
  ("le",          "le"),
  ("neg",         "neg"),
  ("add",         "add"),
  ("sub",         "sub"),
  ("mul1",        "mul"),
  ("mul2",        "mul"),
  ("div",         "div"),
  ("log",         "log"),
  ("exp",         "exp")]

partial def CvxLean.Tree.adjustOps (t : Tree String String) :
  MetaM (Tree String String) := do
  match t with
  | Tree.node op children =>
      if let some op' := Convexify.opMap.find? op then
        let children' ← children.mapM adjustOps
        return Tree.node op' children'
      else
        throwError s!"The atom {op} is not supported by the `convexify` tactic."
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
      throwError "Sexp to Tree conversion error: unexpected empty list"
    else
      match l.head! with
      | .atom op =>
        let children ← l.tail.mapM toTree
        return CvxLean.Tree.node op (Array.mk children)
      | .list _ => throwError "Sexp to Tree conversion error: unexpected list as operator"

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
    | _ => throwError "Tree to Expr conversion error: unexpected num {s}"
  -- Variables.
  | Tree.node "var" #[Tree.leaf s] =>
    if s ∈ vars then
      return mkFVar (FVarId.mk (Name.mkSimple s))
    else
      throwError "Tree to Expr conversion error: unexpected var {s}"
  -- And.
  | Tree.node "and" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkApp2 (mkConst ``And) t1 t2
  -- Equality.
  | Tree.node "eq" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkApp2 (mkConst ``Eq) t1 t2
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
  -- Addition.
  | Tree.node "add" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    let i := mkAppN (mkConst ``instHAdd [levelZero])
      #[(mkConst ``Real), (mkConst ``Real.instAddReal)]
    return mkAppN
      (mkConst ``HAdd.hAdd [levelZero, levelZero, levelZero])
      #[(mkConst ``Real), (mkConst ``Real), (mkConst ``Real), i, t1, t2]
  -- Subtraction.
  | Tree.node "sub" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkAppN
      (mkConst ``Sub.sub ([levelZero] : List Level))
      #[(mkConst ``Real), (mkConst ``Real.instSubReal), t1, t2]
  -- Multiplication.
  | Tree.node "mul" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    let i := mkAppN (mkConst ``instHMul [levelZero])
      #[(mkConst ``Real), (mkConst ``Real.instMulReal)]
    return mkAppN
      (mkConst ``HMul.hMul [levelZero, levelZero, levelZero])
      #[(mkConst ``Real), (mkConst ``Real), (mkConst ``Real), i, t1, t2]
  -- Division.
  | Tree.node "div" #[t1, t2] => do
    let t1 ← treeToExpr vars t1
    let t2 ← treeToExpr vars t2
    return mkAppN
      (mkConst ``Div.div ([levelZero] : List Level))
      #[(mkConst ``Real), (mkConst ``Real.instDivReal), t1, t2]
  -- Log.
  | Tree.node "log" #[t] => do
    let t ← treeToExpr vars t
    return mkAppN (mkConst ``Real.log) #[t]
  -- Exp.
  | Tree.node "exp" #[t] => do
    let t ← treeToExpr vars t
    return mkAppN (mkConst ``Real.exp) #[t]
  -- Error.
  | Tree.node op children =>
    throwError "Tree to Expr conversion error: unexpected op {op} with {children.size} children"

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
  | _ => throwError "Tree to SolutionExpr conversion error: unexpected tree structure"

def CvxLean.stringToSolutionExpr (vars : List Name) (s : String) :
  MetaM (Meta.SolutionExpr) := do
  let t ← stringToTree s
  match ← treeToSolutionExpr vars t with
  | some se => return se
  | none => throwError "String to SolutionExpr conversion error"

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

-- TODO(RFM): Not hard-coded.
def findTactic (s : String) : MetaM Syntax := do
  match s with
  | "mul-exp" =>
    return ← `(tactic| internally_do (rw [Real.exp_add] <;> positivity))
  | "le-log" =>
    return ← `(tactic| internally_do (rw [Real.log_le_log] <;> positivity))
  | "log-exp" =>
    return ← `(tactic| internally_do (rw [Real.log_exp]))
  | _ => throwError "Unknown rewrite name."

elab "convexify" : tactic => withMainContext do
  let g ← getMainGoal

  let gExpr ← Meta.matchSolutionExpr g
  let vars ← withLambdaBody gExpr.constraints fun p _ => do
    let pr ← Meta.mkProjections gExpr.domain p
    return pr.map (Prod.fst)
  let varsStr := vars.map toString

  let gStr ← DCP.uncheckedTreeString gExpr varsStr
  dbg_trace s!"Goal: {gStr}"

  let eggRequest := {
    target := gStr
  }
  let steps := ← runEggRequest eggRequest

  for step in steps do
    let g ← getMainGoal
    let gExpr ← Meta.matchSolutionExpr g

    let expectedTerm := step.expectedTerm
    let expectedSolutionExpr ← stringToSolutionExpr vars expectedTerm
    let expectedExpr := expectedSolutionExpr.toExpr
    let eq ← mkAppM `Eq #[expectedExpr, gExpr.toExpr]
    let gs ← g.apply (← mkAppM `Eq.mp #[← mkFreshExprMVar eq])
    let gs1 ← evalTacticAt (← findTactic step.rewriteName) gs[1]!
    if gs1.length == 0 then
      replaceMainGoal gs
    else
      replaceMainGoal gs
      throwError "Failed to rewrite goal."

  return ()

open Minimization Real

lemma test : Solution (
    optimization (x y : ℝ)
      minimize (x * y)
      subject to
        hx : 0 < x
        hy : 0 < y
        h : x * y ≤ (10.123)
) := by
  map_exp
  convexify
  sorry
