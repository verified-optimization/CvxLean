import Lean 

open Lean Elab Meta Tactic Term IO

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

def parseEggResponse (responseString : String) : MetaM (Array String) := do
  dbg_trace s!"Egg response: {responseString}"
  let outJson : Json ← match Json.parse responseString with
    | Except.error e => throwError "JSON parsing error: {e}."
    | Except.ok j => pure j
    
  let responseType := (outJson.getObjValD "response").getStr!

  if responseType == "error" then 
    throwError "Error calling egg."
  else
    let steps ← liftExcept  <| outJson.getObjVal? "steps"
    let steps ← liftExcept <| Json.getArr? steps

    return steps.map Json.pretty

def runEggRequest (request : EggRequest) : MetaM (Array String) :=
  dbg_trace s!"Running egg request: {request.toJson}"
  runEggRequestRaw request.toJson >>= parseEggResponse

elab "convexify" : tactic => withMainContext do
  let g ← getMainGoal 

  let eggRequest := {
    target := "(mul (exp (var x)) (exp (var y)))"
  }
  let steps := ← runEggRequest eggRequest
  
  for step in steps do
    IO.println step

  return ()

example : True := by
  convexify 
  trivial

