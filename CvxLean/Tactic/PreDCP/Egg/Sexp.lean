import Lean

open Lean

-- Taken from https://github.com/opencompl/egg-tactic-code

inductive Sexp
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving BEq, Inhabited, Repr

def Sexp.fromString : String → Sexp
  | s => Sexp.atom s

instance : Coe String Sexp where
  coe s := Sexp.fromString s

def Sexp.fromList : List Sexp → Sexp
  | xs => Sexp.list xs

instance : Coe (List Sexp) Sexp where
  coe := Sexp.fromList

partial def Sexp.toString : Sexp → String
  | .atom s  => s
  | .list xs => "(" ++ " ".intercalate (xs.map Sexp.toString) ++ ")"

instance : ToString Sexp := ⟨Sexp.toString⟩

def Sexp.toList? : Sexp → Option (List Sexp)
  | .atom _  => none
  | .list xs => some xs

def Sexp.toAtom! : Sexp → String
  | .atom s  => s
  | .list xs => panic! s!"expected atom, found list at {List.toString xs}"

inductive SexpTok
  | sexp : Sexp →  SexpTok
  | opening : String.Pos → SexpTok
  deriving BEq, Inhabited, Repr

structure SexpState where
  it : String.Iterator
  stack : List SexpTok := []
  sexps : List Sexp := []
  depth : Nat := 0
  deriving BEq, Repr

def SexpState.fromString (s : String) : SexpState where
  it := s.iter

instance : Inhabited SexpState where
  default := SexpState.fromString ""

inductive SexpError
  | unmatchedOpenParen (ix: String.Iterator) : SexpError
  | unmatchedCloseParen (ix: String.Iterator) : SexpError
  | notSingleSexp (s: String) (xs: List Sexp) : SexpError
  deriving BEq, Repr

instance : ToString SexpError where
  toString
    | .unmatchedOpenParen ix => s!"Unmatched open parenthesis at {ix}"
    | .unmatchedCloseParen ix => s!"Unmatched close parenthesis at {ix}"
    | .notSingleSexp s xs => s!"not a single sexp '{s}', parsed as: '{xs}'"

abbrev SexpM := EStateM SexpError SexpState

def SexpM.peek : SexpM (Option (Char × String.Pos)) := do
  let state ← get
  return if state.it.atEnd then none else some (state.it.curr, state.it.i)

def SexpM.curPos : SexpM String.Pos := do
  let state ← get
  return state.it.i

def SexpM.mkSubstring (l : String.Pos) (r : String.Pos) : SexpM Substring := do
  let state ← get
  return { str := state.it.s, startPos := l, stopPos := r}

def SexpM.advance: SexpM Unit := do
  modify (fun state => { state with it := state.it.next })

def SexpM.pushTok (tok: SexpTok): SexpM Unit := do
  modify (fun state => { state with stack := tok :: state.stack })

def SexpM.pushSexp (sexp: Sexp): SexpM Unit := do
  let state ← get
  if state.stack.length == 0 then
    set { state with stack := [], sexps := sexp :: state.sexps }
  else
    set { state with stack := (SexpTok.sexp sexp) :: state.stack }

def SexpM.incrementDepth: SexpM Unit :=
  modify (fun state => { state with depth := state.depth + 1 })

def SexpM.decrementDepth: SexpM Unit :=
  modify (fun state => { state with depth := state.depth - 1 })

instance {α} [Inhabited α] : Inhabited (SexpM α) := by infer_instance

def SexpM.pop: SexpM SexpTok := do
  let state ← get
  match state.stack with
  | [] => panic! "empty stack"
  | x :: xs =>
      set { state with stack := xs }
      return x

-- Remove elements from the stack of tokens `List SexpToken` till we find a `SexpToken.opening`.
-- When we do, return (1) the position of the open paren, (2) the list of SexpTokens left on the stack, and (3) the list of Sexps
-- Until then, accumulate the `SexpToken.sexp`s into `sexps`.
def stackPopTillOpen (stk : List SexpTok) (sexps : List Sexp := []) :
  Option (String.Pos × (List SexpTok) × (List Sexp)) :=
  match stk with
  | [] => .none
  | SexpTok.opening openPos :: rest => (.some (openPos, rest, sexps))
  | SexpTok.sexp s :: rest => stackPopTillOpen rest (s :: sexps)

/-- Collapse the current stack till the last ( into a single `Sexp.list`. -/
def SexpM.matchClosingParen: SexpM Unit := do
  let state ← get
  match stackPopTillOpen state.stack with
  | some (_, stk, sexps) =>
      let sexp := Sexp.list sexps
      modify (fun state => { state with stack := stk })
      SexpM.pushSexp sexp
  | none => throw (SexpError.unmatchedCloseParen state.it)

partial def SexpM.takeString (startPos : String.Pos) : SexpM Substring := do
  match (← SexpM.peek) with
  | none => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some (' ', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some ('(', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some (')', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some _ => do
      SexpM.advance
      SexpM.takeString startPos

partial def SexpM.parse : SexpM Unit := do
  match (← SexpM.peek) with
  | some ('(', i) => do
      SexpM.advance
      SexpM.pushTok (SexpTok.opening i)
      SexpM.incrementDepth
      SexpM.parse
  | some (')', _) => do
      SexpM.advance
      SexpM.matchClosingParen
      SexpM.parse
  | some (' ', _) => do
      SexpM.advance
      SexpM.parse
  | some (_, i) => do
      let s ← SexpM.takeString i
      SexpM.pushSexp ((Sexp.atom s.toString))
      SexpM.parse
  | .none => do
      let state ← get
      match stackPopTillOpen state.stack with
      | some (openPos, _, _) => throw <|
          SexpError.unmatchedOpenParen ({ s := state.it.s, i := openPos })
      | none => return ()

/-- Parse a list of (possibly empty) sexps. -/
def parseSexpList (s: String):  Except SexpError (List Sexp) :=
  let initState := SexpState.fromString s
  match EStateM.run SexpM.parse initState with
  | .ok () state => .ok state.sexps.reverse
  | .error e _ => .error e

/-- Parse a single s-expression, and error if found no sexp or multiple sexps.
-/
def parseSingleSexp (s: String) : Except SexpError Sexp := do
  match (← parseSexpList s) with
  | [x] => .ok x
  | xs => .error (.notSingleSexp s xs)
