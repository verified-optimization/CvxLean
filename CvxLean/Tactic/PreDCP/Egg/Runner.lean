import Lean

open Lean

-- Taken from https://github.com/opencompl/egg-tactic-code

def _root_.Lean.Json.getStr! (j : Json) : String :=
  match j with
  | Json.str a => a
  | _ => ""

def _root_.Lean.Json.getArr! (j : Json) : Array Json :=
  match j with
  | Json.arr a => a
  | _ => #[]

def _root_.MetaM.ofExcept [ToString ε]: Except ε α -> MetaM α :=
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

namespace CvxLean

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

  if responseType == "Error" then
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

/-- -/
def runEggRequest (request : EggRequest) : MetaM (Array EggRewrite) :=
  dbg_trace s!"Running egg request: {request.toJson}"
  runEggRequestRaw request.toJson >>= parseEggResponse

end CvxLean
