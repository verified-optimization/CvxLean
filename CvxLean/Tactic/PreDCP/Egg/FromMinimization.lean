import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.PreDCP.UncheckedDCP

namespace CvxLean

section Egg.FromMinimization

open Lean

/-- Flatten an `EggTree` to a string to send to egg. -/
partial def _root_.EggTree.toEggString : Tree String String → String
  | Tree.node n children =>
    let childrenStr := (children.map EggTree.toEggString).data
    "(" ++ n ++ " " ++ (" ".intercalate childrenStr) ++ ")"
  | Tree.leaf n => n

/-- -/
def _root_.EggTree.ofOCTree (ocTree : OC (String × Tree String String)) :
  Tree String String :=
  let objFun := ocTree.objFun.2
  let constrs := ocTree.constr.map 
    fun (h, c) => Tree.node "constr" #[Tree.leaf h, c]
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constrs" constrs
  Tree.node "prob" #[objFunNode, constrNode]

/-- Add the constructor `var` around every variable in the tree. -/
partial def _root_.EggTree.surroundVars (t : Tree String String) (vars : List String) :=
  match t with
  | Tree.leaf s => if s ∈ vars then Tree.node "var" #[Tree.leaf s] else t
  | Tree.node n children => Tree.node n (children.map (surroundVars · vars))

/-- Mapping between atom names that come from the unchecked tree construction
and their egg counterparts. `prob`, `objFun`, `constr` and `constrs` are special
cases. The rest of names come from the atom library. It also returns the arity 
of the operation and some extra arguments. -/
def _root_.EggTree.opMap : HashMap String (String × Nat × Array String) :=
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
    ("lt",          ("lt", 2, #[])),
    ("neg",         ("neg", 1, #[])),
    ("add",         ("add", 2, #[])),
    ("sub",         ("sub", 2, #[])),
    ("mul1",        ("mul", 2, #[])),
    ("mul2",        ("mul", 2, #[])),
    ("sq",          ("pow", 1, #["2"])),
    ("sqrt",        ("sqrt", 1, #[])),
    ("sqrt'",       ("sqrt", 1, #[])),
    ("div",         ("div", 2, #[])),
    ("log",         ("log", 1, #[])),
    ("exp",         ("exp", 1, #[]))
  ]

/-- Traverse the tree and use `EggTree.opMap` to align the names of the 
constructors. -/
partial def _root_.EggTree.adjustOps (t : Tree String String) :
  MetaM (Tree String String) := do
  match t with
  | Tree.node op children =>
      if let some (op', arity, extraArgs) := EggTree.opMap.find? op then
        if children.size ≠ arity && op' != "constrs" then
          throwError s!"The operator {op} has arity {children.size}, but it should have arity {arity}."
        let children' ← children.mapM adjustOps
        let children' := children' ++ extraArgs.map Tree.leaf
        return Tree.node op' children'
      else
        throwError s!"The atom {op} is not supported by the `convexify` tactic."
  | Tree.leaf "unknown" => throwError "Unknown atom."
  | l => return l

/-- Given an expression representing a minimization problem, turn it into a 
tree of strings, also extract all the domain information for single varibales,
in particular positivity and nonnegativity constraints. -/
def _root_.ExtendedEggTree.fromMinimization (e : Meta.MinimizationExpr) (vars : List String) :
  MetaM (OC (String × Tree String String) × Array (String × String × String)) := do
  let ocTree ← UncheckedDCP.uncheckedTreeFromMinimizationExpr e
  -- NOTE: Detect domain constraints. This only works for very simple variable 
  -- constraints. A better approach would be to detect these constraints when
  -- building the unchecked DCP tree.
  let nonnegVars := ocTree.constr.filterMap <| fun (h, c) =>
    match c with
    | Tree.node "le" #[Tree.leaf s, Tree.leaf v] => 
        if let some i := s.toInt? then
          if i = 0 && v ∈ vars then some (h, v) else none 
        else none
    | _ => none
  let posVars := ocTree.constr.filterMap <| fun (h, c) =>
    match c with
    | Tree.node "lt" #[Tree.leaf s, Tree.leaf v] => 
        if let some i := s.toInt? then
          if i ≥ 0 && v ∈ vars then some (h, v) else none 
        else none
    | Tree.node "le" #[Tree.leaf s, Tree.leaf v] => 
        if let some i := s.toInt? then
          if i > 0 && v ∈ vars then some (h, v) else none 
        else none
    -- Special case to handle common constraints of the form n/d <= x.
    | Tree.node "le" #[Tree.node "div" #[Tree.leaf n, Tree.leaf d], Tree.leaf v] => 
        if let some ni := n.toInt? then
          if let some di := d.toInt? then 
            if ni ≥ 0 && di ≥ 0 && v ∈ vars then some (h, v) else none 
          else none
        else none
    | _ => none

  let domainConstrs := 
    (nonnegVars.map (fun (h, v) => (h, v, "NonNeg"))) ++ 
    (posVars.map (fun (h, v) => (h, v, "Pos")))

  -- Surround variables and adjust operations in the whole tree.
  let ocTree : OC (String × Tree String String) := { 
    objFun := let (ho, o) := ocTree.objFun; (ho, EggTree.surroundVars o vars)
    constr := ocTree.constr.map (fun (h, c) => (h, EggTree.surroundVars c vars)) }
  let ocTree : OC (String × Tree String String) := {
    objFun := (ocTree.objFun.1, ← EggTree.adjustOps ocTree.objFun.2)
    constr := ← ocTree.constr.mapM (fun (h, c) => return (h, ← EggTree.adjustOps c)) }
  return (ocTree, domainConstrs)

end Egg.FromMinimization

end CvxLean
