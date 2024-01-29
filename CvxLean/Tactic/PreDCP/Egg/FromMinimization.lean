import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.PreDCP.UncheckedDCP
import CvxLean.Tactic.PreDCP.Egg.EggTypes

namespace CvxLean

section Egg.FromMinimization

open Lean

/-- Add the constructor `var` around every variable in the tree. -/
partial def EggTree.surroundVars (t : Tree String String) (vars : List String) :=
  match t with
  | Tree.leaf s =>
      if s ∈ vars then
        Tree.node "var" #[Tree.leaf s]
      else
        Tree.node "param" #[Tree.leaf s]
  | Tree.node n children => Tree.node n (children.map (surroundVars · vars))

inductive EggTree.OpArgTag
  | arg
  | val (s : String)

/-- Mapping between atom names that come from the unchecked tree construction
and their egg counterparts. `prob`, `objFun`, `constr` and `constrs` are special
cases. The rest of names come from the atom library. It also returns the arity
of the operation and some extra arguments. -/
def EggTree.opMap : HashMap String (String × Array EggTree.OpArgTag) :=
  HashMap.ofList [
    ("prob",        ("prob",    #[.arg, .arg])),
    ("objFun",      ("objFun",  #[.arg])),
    ("constr",      ("constr",  #[.arg, .arg])),
    ("constrs",     ("constrs", #[])),
    ("maximizeNeg", ("neg",     #[.arg])),
    ("var",         ("var",     #[.arg])),
    ("param",       ("param",   #[.arg])),
    ("eq",          ("eq",      #[.arg, .arg])),
    ("le",          ("le",      #[.arg, .arg])),
    ("lt",          ("lt",      #[.arg, .arg])),
    ("neg",         ("neg",     #[.arg])),
    ("inv",         ("inv",     #[.arg])),
    ("oneDiv",      ("div",     #[.val "1", .arg])),
    ("abs",         ("abs",     #[.arg])),
    ("sqrt",        ("sqrt",    #[.arg])),
    ("powOne",      ("pow",     #[.arg, .val "1"])),
    ("sq",          ("pow",     #[.arg, .val "2"])),
    ("powNegOne",   ("pow",     #[.arg, .val "-1"])),
    ("powNegTwo",   ("pow",     #[.arg, .val "-2"])),
    ("log",         ("log",     #[.arg])),
    ("exp",         ("exp",     #[.arg])),
    ("xexp",        ("xexp",    #[.arg])),
    ("entr",        ("entr",    #[.arg])),
    ("min",         ("min",     #[.arg, .arg])),
    ("max",         ("max",     #[.arg, .arg])),
    ("add",         ("add",     #[.arg, .arg])),
    ("sub",         ("sub",     #[.arg, .arg])),
    ("mul1",        ("mul",     #[.arg, .arg])),
    ("mul2",        ("mul",     #[.arg, .arg])),
    ("div",         ("div",     #[.arg, .arg])),
    ("quadOverLin", ("qol",     #[.arg, .arg])),
    ("geoMean",     ("geo",     #[.arg, .arg])),
    ("logSumExp₂",  ("lse",     #[.arg, .arg])),
    ("norm2₂",      ("norm2",   #[.arg, .arg]))
  ]

/-- Traverse the tree and use `EggTree.opMap` to align the names of the
constructors. -/
partial def EggTree.adjustOps (t : Tree String String) : MetaM (Tree String String) := do
  match t with
  | Tree.node op children =>
      if let some (newOp, argTags) := EggTree.opMap.find? op then
        let mut children ← children.mapM adjustOps
        let argsGiven := children.size
        let mut newChildren := #[]
        let mut arityError := false
        for argTag in argTags do
          match argTag with
          | .arg =>
              if children.size > 0 then
                newChildren := newChildren.push children[0]!
                children := children.drop 1
              else
                arityError := true
                break
          | .val s =>
              newChildren := newChildren.push (Tree.leaf s)
        arityError := arityError || children.size > 0
        if arityError then
          throwError s!"The op {op} was passed {argsGiven} arguments."
        else
        return Tree.node newOp newChildren
      else
        throwError s!"The atom {op} is not supported by the `convexify` tactic."
  | Tree.leaf "unknown" => throwError "Unknown atom."
  | l => return l

def _root_.Option.map2 {α β γ} (f : α → β → γ) : Option α → Option β → Option γ
  | some a, some b => some <| f a b
  | _, _ => none

/-- Extract the numerical value from the egg tree, if any. This is used to
construct the domain information needed in the e-class analyses.
NOTE(RFM): This is a source of inaccuracy as some operations are approximate,
however, it does not compromise the soundness of the procedure. If the domains
sent to egg are incorrect, which may lead to an incorrect sequence of steps to,
transform the problem, Lean will reject the proof. -/
partial def EggTree.getNumericalValue? : EggTree → Option Float
  | Tree.leaf s =>
      Option.map Float.ofInt s.toInt?
  | Tree.node "neg" #[(t : EggTree)] =>
      Option.map Float.neg t.getNumericalValue?
  | Tree.node "sqrt" #[(t : EggTree)] =>
      Option.map Float.sqrt t.getNumericalValue?
  | Tree.node "log" #[(t : EggTree)] =>
      Option.map Float.log t.getNumericalValue?
  | Tree.node "exp" #[(t : EggTree)] =>
      Option.map Float.exp t.getNumericalValue?
  | Tree.node "add" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map2 Float.add t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "sub" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map2 Float.sub t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "mul" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map2 Float.mul t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "div" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map2 Float.div t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "pow" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map2 Float.pow t1.getNumericalValue? t2.getNumericalValue?
  | _ => none

/-- -/
def EggTree.getVariableName? (vars : List String) : EggTree → Option String
  | Tree.leaf s => if s ∈ vars then some s else none
  | _ => none

/-- Given an expression representing a minimization problem, turn it into a
tree of strings, also extract all the domain information for single varibales,
in particular positivity and nonnegativity constraints. -/
def ExtendedEggTree.fromMinimization (e : Meta.MinimizationExpr) (vars : List String) :
  MetaM (OC (String × EggTree) × Array (String × String × EggDomain)) := do
  let ocTree ← UncheckedDCP.uncheckedTreeFromMinimizationExpr e
  -- Detect domain constraints. We capture the following cases:
  -- * x ≤ f and f ≤ x,
  -- * x < f and f < x,
  -- * x = f and f = x,
  -- where "x" is a variable name and "f" is a numerical value.
  let mut domainConstrs := #[]
  let mut i := 0
  for (h, c) in ocTree.constr do
    -- NOTE: some constraints may have the same name, so we add the index.
    let h := s!"{i}:" ++ h
    let res :=
      match c with
      | Tree.node "le" #[(tl : EggTree), (tr : EggTree)] =>
          match (tl.getVariableName? vars, tr.getNumericalValue?) with
          | (some v, some f) =>
              -- v ∈ (-inf, f]
              some (h, v, ⟨"-inf", f.toString, "1", "0"⟩)
          | _ =>
            match (tl.getNumericalValue?, tr.getVariableName? vars) with
            | (some f, some v) =>
                -- v ∈ [f, inf)
                some (h, v, ⟨f.toString, "inf", "0", "1"⟩)
            | _ => none
      | Tree.node "lt" #[(tl : EggTree), (tr : EggTree)] =>
          match (tl.getVariableName? vars, tr.getNumericalValue?) with
          | (some v, some f) =>
              -- v ∈ (-inf, f)
              some (h, v, ⟨"-inf", f.toString, "1", "1"⟩)
          | _ =>
            match (tl.getNumericalValue?, tr.getVariableName? vars) with
            | (some f, some v) =>
                -- v ∈ (f, inf)
                some (h, v, ⟨f.toString, "inf", "1", "1"⟩)
            | _ => none
      | Tree.node "eq" #[(tl : EggTree), (tr : EggTree)] =>
          match (tl.getVariableName? vars, tr.getNumericalValue?) with
          | (some v, some f) =>
              -- v ∈ [f, f]
              some (h, v, ⟨f.toString, f.toString, "0", "0"⟩)
          | _ =>
            match (tl.getNumericalValue?, tr.getVariableName? vars) with
            | (some f, some v) =>
                -- v ∈ [f, f]
                some (h, v, ⟨f.toString, f.toString, "0", "0"⟩)
            | _ => none
      | _ => none
    match res with
    | some r => domainConstrs := domainConstrs.push r
    | none => pure ()
    i := i + 1

  -- Surround variables and adjust operations in the whole tree.
  let ocTree : OC (String × Tree String String) := {
    objFun := let (ho, o) := ocTree.objFun; (ho, EggTree.surroundVars o vars)
    constr := ocTree.constr.map (fun (h, c) => (h, EggTree.surroundVars c vars)) }
  let ocTree : OC (String × Tree String String) := {
    objFun := (ocTree.objFun.1, ← EggTree.adjustOps ocTree.objFun.2)
    constr := ← ocTree.constr.mapIdxM <|
      -- TODO: some constraints may have the same name, so we add the index.
      fun i (h, c) => return (s!"{i}:" ++ h, ← EggTree.adjustOps c) }
  return (ocTree, domainConstrs)

/-- Flatten an `EggTree` to a string to send to egg. -/
partial def EggTree.toEggString : Tree String String → String
  | Tree.node n children =>
    let childrenStr := (children.map EggTree.toEggString).data
    "(" ++ n ++ " " ++ (" ".intercalate childrenStr) ++ ")"
  | Tree.leaf n => n

/-- Size of the AST. -/
partial def EggTree.size : EggTree → Nat
  | Tree.node _ children => 1 + (children.map EggTree.size).foldl Nat.add 0
  | Tree.leaf _ => 1

/-- -/
def EggTree.ofOCTree (ocTree : OC (String × Tree String String)) : Tree String String :=
  let objFun := ocTree.objFun.2
  let constrs := ocTree.constr.map
    fun (h, c) => Tree.node "constr" #[Tree.leaf h, c]
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constrs" constrs
  Tree.node "prob" #[objFunNode, constrNode]

/-- Convert `OC` tree to `EggMinimization`. -/
def EggMinimization.ofOCTree (oc : OC (String × EggTree)) : EggMinimization :=
  { objFun := EggTree.toEggString oc.objFun.2,
    constrs := Array.data <| oc.constr.map fun (h, c) => (h, EggTree.toEggString c) }

end Egg.FromMinimization

end CvxLean
