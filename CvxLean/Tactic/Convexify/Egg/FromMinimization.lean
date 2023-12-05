import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.Convexify.UncheckedDCP
import CvxLean.Tactic.Convexify.Egg.EggTypes

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

def _root_.Option.map2 {α β γ} (f : α → β → γ) : Option α → Option β → Option γ
  | some a, some b => some <| f a b
  | _, _ => none

/-- Extract the numerical value from the egg tree, if any. This is used to
construct the domain information needed in the e-class analyses.
NOTE(RFM): This is a source of inaccuracy as some operations are approximate,
however, it does not compromise the soundness of the procedure. If the domains
sent to egg are incorrect, which may lead to an incorrect sequence of steps to,
transform the problem, Lean will reject the proof. -/
partial def _root_.EggTree.getNumericalValue? : EggTree → Option Float
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
def _root_.EggTree.getVariableName? (vars : List String) : EggTree → Option String
  | Tree.leaf s => if s ∈ vars then some s else none
  | _ => none

/-- Given an expression representing a minimization problem, turn it into a
tree of strings, also extract all the domain information for single varibales,
in particular positivity and nonnegativity constraints. -/
def _root_.ExtendedEggTree.fromMinimization (e : Meta.MinimizationExpr) (vars : List String) :
  MetaM (OC (String × EggTree) × Array (String × String × EggDomain)) := do
  let ocTree ← UncheckedDCP.uncheckedTreeFromMinimizationExpr e
  -- Detect domain constraints. We capture the following cases:
  -- * x ≤ f and f ≤ x,
  -- * x < f and f < x,
  -- * x = f and f = x,
  -- where "x" is a variable name and "f" is a numerical value.
  let domainConstrs := ocTree.constr.filterMap <| fun (h, c) =>
    match c with
    | Tree.node "le" #[(tl : EggTree), (tr : EggTree)] =>
        match (tl.getVariableName? vars, tr.getNumericalValue?) with
        | (some v, some f) =>
            -- v ∈ [-inf, f]
            some (h, v, ⟨"-inf", f.toString, "0", "0"⟩)
        | _ =>
          match (tl.getNumericalValue?, tr.getVariableName? vars) with
          | (some f, some v) =>
              -- v ∈ [f, inf]
              some (h, v, ⟨f.toString, "inf", "0", "0"⟩)
          | _ => none
    | Tree.node "lt" #[(tl : EggTree), (tr : EggTree)] =>
        match (tl.getVariableName? vars, tr.getNumericalValue?) with
        | (some v, some f) =>
            -- v ∈ [-inf, f)
            some (h, v, ⟨"-inf", f.toString, "0", "1"⟩)
        | _ =>
          match (tl.getNumericalValue?, tr.getVariableName? vars) with
          | (some f, some v) =>
              -- v ∈ (f, inf]
              some (h, v, ⟨f.toString, "inf", "1", "0"⟩)
          | _ => none
    | Tree.node "eq" #[(tl : EggTree), (tr : EggTree)] =>
        match (tl.getVariableName? vars, tr.getNumericalValue?) with
        | (some v, some f) =>
            -- v ∈ [f, f]
            some (h, v, ⟨f.toString, f.toString, "1", "1"⟩)
        | _ =>
          match (tl.getNumericalValue?, tr.getVariableName? vars) with
          | (some f, some v) =>
              -- v ∈ [f, f]
              some (h, v, ⟨f.toString, f.toString, "1", "1"⟩)
          | _ => none
    | _ => none

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
