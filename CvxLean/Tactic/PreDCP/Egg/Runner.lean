import Lean
import CvxLean.Tactic.PreDCP.Egg.EggTypes

/-!
# Call the `egg` sub-process and get a list of rewrites

This file defines the `runEggRequest` function, which is used to call the `egg` sub-process. Some
pre-processing is necessary to encode domains and minimization problems into the JSON. Also, some
post-processing is needed to parse the JSON response.

Taken from <https://github.com/opencompl/egg-tactic-code>/
-/

namespace CvxLean

open Lean

def _root_.Lean.Json.getStr! (j : Json) : String :=
  match j with
  | Json.str a => a
  | _ => ""

def _root_.Lean.Json.getArr! (j : Json) : Array Json :=
  match j with
  | Json.arr a => a
  | _ => #[]

variable {ε α}

def _root_.MetaM.ofExcept [ToString ε]: Except ε α → MetaM α :=
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

/-- JSONify an EggMinimization.
NOTE: Tuples are lists of two elements. -/
def EggMinimization.toJson (e : EggMinimization) : String :=
  "{" ++
  surroundQuotes "obj_fun" ++ " : " ++ surroundQuotes e.objFun ++ ", " ++
  surroundQuotes "constrs" ++ " : " ++
    "[" ++
      (", ".intercalate <| e.constrs.map (fun constr =>
        "["  ++ (surroundQuotes constr.1) ++          -- Constraint name.
        ", " ++ (surroundQuotes constr.2) ++ "]")) ++ -- Constraint expression.
    "]" ++
  "}"

def EggDomain.toJson (e : EggDomain) : String :=
  "[" ++
  surroundQuotes e.hi ++ ", " ++
  surroundQuotes e.lo ++ ", " ++
  surroundQuotes e.hi_open ++ ", " ++
  surroundQuotes e.lo_open ++
  "]"

/-- JSONify an `EggRequest`.
NOTE: Tuples are lists of two elements. -/
def EggRequest.toJson (e : EggRequest) : String :=
  "{" ++
  surroundQuotes "request" ++ " : " ++ surroundQuotes "PerformRewrite" ++ ", " ++
  surroundQuotes "prob_name" ++ " : " ++ surroundQuotes e.probName ++ ", " ++
  surroundQuotes "domains" ++ " : " ++
    "[" ++
      (", ".intercalate <| e.domains.map (fun domain =>
        "[" ++ (surroundQuotes domain.1) ++ -- Variable name.
        ", " ++ domain.2.toJson ++ "]")) ++ -- Encoded interval.
    "]" ++ ", " ++
  surroundQuotes "target" ++ " : " ++ (e.target.toJson) ++
  "}"


def EggRewriteDirection.toString : EggRewriteDirection → String
  | Forward => "fwd"
  | Backward => "bwd"

instance : ToString EggRewriteDirection where
  toString := EggRewriteDirection.toString

def EggRewrite.toString (e : EggRewrite) : String :=
  "{" ++
  surroundQuotes "rewrite_name" ++ " : " ++ surroundQuotes e.rewriteName ++ ", " ++
  surroundQuotes "direction" ++ " : " ++ surroundQuotes (e.direction.toString) ++ ", " ++
  surroundQuotes "location" ++ " : " ++ surroundQuotes e.location ++ ", " ++
  surroundQuotes "subexpr_from" ++ " : " ++ surroundQuotes e.subexprFrom ++ ", " ++
  surroundQuotes "subexpr_to" ++ " : " ++ surroundQuotes e.subexprTo ++ ", " ++
  surroundQuotes "expected_term" ++ " : " ++ surroundQuotes e.expectedTerm ++
  "}"

instance : ToString EggRewrite where
  toString := EggRewrite.toString

/-- Call the `egg` sub-process by runnning the executable `egg-pre-dcp/utils/egg-pre-dcp`, generated
by running `lake build EggPreDCP`. The input is passed via standard input. -/
def runEggRequestRaw (requestJson : String) : MetaM String := do
  let eggProcess ← IO.Process.spawn {
      cmd    := "egg-pre-dcp/utils/egg-pre-dcp",
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

/-- Read `egg`'s output and trun it into an array of `EggRewrite`s. -/
def parseEggResponse (responseString : String) :
    MetaM (HashMap String (Array EggRewrite)) := do
  dbg_trace s!"Egg response: {responseString}"
  let outJson : Json ← match Json.parse responseString with
    | Except.error e => throwError (s!"error calling `egg`, JSON parsing error ({e}).")
    | Except.ok j => pure j

  let responseType := (outJson.getObjValD "response").getStr!

  if responseType == "Error" then
    match (outJson.getObjValD "error").getStr? with
    | Except.error _ => throwError "error calling `egg`."
    | Except.ok errorMessage => throwError "from `egg` (\"{errorMessage}\")."

  else
    let steps ← liftExcept <| outJson.getObjVal? "steps"
    let steps ← liftExcept <| Json.getObj? steps

    let mut res := HashMap.empty
    for ⟨componentName, componentSteps⟩ in steps.toArray do
      let componentSteps ← liftExcept <| Json.getArr? componentSteps
      let componentStepsParsed : Array EggRewrite := componentSteps.map fun step =>
        let rewriteName := (step.getObjValD "rewrite_name").getStr!
        let direction := match (step.getObjValD "direction").getStr! with
          | "Forward" => EggRewriteDirection.Forward
          | "Backward" => EggRewriteDirection.Backward
          | _ => panic! "Unexpected rewrite direction."
        let location := (step.getObjValD "location").getStr!
        let subexprFrom := (step.getObjValD "subexpr_from").getStr!
        let subexprTo := (step.getObjValD "subexpr_to").getStr!
        let expectedTerm := (step.getObjValD "expected_term").getStr!
        { rewriteName  := rewriteName,
          direction    := direction,
          location     := location,
          subexprFrom  := subexprFrom,
          subexprTo    := subexprTo,
          expectedTerm := expectedTerm }
      res := res.insert componentName componentStepsParsed

    return res

/-- Run request to `egg` and parse the output to get an array of rewrites, if successful. -/
def runEggRequest (request : EggRequest) : MetaM (HashMap String (Array EggRewrite)) :=
  dbg_trace s!"Running egg request: {request.toJson}"
  runEggRequestRaw request.toJson >>= parseEggResponse

end CvxLean
