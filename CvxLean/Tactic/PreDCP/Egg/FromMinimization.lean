import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.PreDCP.Egg.UncheckedDCP
import CvxLean.Tactic.PreDCP.Egg.EggTypes

/-!
# Minimization problem to Egg minimization (S-expressions)

Using `CvxLean/Tactic/PreDCP/Egg/UncheckedDCP.lean`, we build an atom tree from a given problem,
ignoring the curvature checks. This file does all the processing needed after that point to turn
it into a problem that can be sent to `egg`. This includes:
* Adjusting the name of the constructors.
* Building the domain for each variable in normalized linear constraint to initialize the e-class
  analyses.
* Flattening the trees to strings.
-/

namespace CvxLean

open Lean Meta

namespace EggTree

/-- Mapping between atom names that come from the unchecked tree construction and their `egg`
counterparts. `prob`, `objFun`, `constr` and `constrs` are special cases. The rest of names come
from the atom library. It also returns the extra arguments, which sometimes may be pre-determined,
for example, the atom `powNegOne` corresponds to the constructor `pow` in the `egg` language with
the second argumetn set to `-1`. -/
def opMap : HashMap String (String × Array EggTreeOpArgTag) :=
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
    ("mul",         ("mul",     #[.arg, .arg])),
    ("mul1",        ("mul",     #[.arg, .arg])),
    ("mul2",        ("mul",     #[.arg, .arg])),
    ("div",         ("div",     #[.arg, .arg])),
    ("quadOverLin", ("qol",     #[.arg, .arg])),
    ("geoMean",     ("geo",     #[.arg, .arg])),
    ("logSumExp₂",  ("lse",     #[.arg, .arg])),
    ("norm2₂",      ("norm2",   #[.arg, .arg]))
  ]

/-- Traverse the tree and use `opMap` to align the names of the constructors. -/
partial def adjustOps (t : EggTree) : MetaM EggTree := do
  match t with
  | Tree.node op children =>
      if let some (newOp, argTags) := opMap.find? op then
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
        throwError s!"The atom {op} is not supported by the `pre_dcp` tactic."
  | Tree.leaf "unknown" => throwError "Unknown atom."
  | l => return l

/-- Extract the numerical value from the egg tree, if any. This is used to construct the domain
information needed in the e-class analyses.
NOTE: This is a source of inaccuracy as some operations are approximate, however, it does not
compromise the soundness of the procedure. If the domains sent to egg are incorrect, which may lead
to an incorrect sequence of steps to, transform the problem, Lean will reject the proof. -/
partial def getNumericalValue? : EggTree → Option Float
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
      Option.map₂ Float.add t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "sub" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map₂ Float.sub t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "mul" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map₂ Float.mul t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "div" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map₂ Float.div t1.getNumericalValue? t2.getNumericalValue?
  | Tree.node "pow" #[(t1 : EggTree), (t2 : EggTree)] =>
      Option.map₂ Float.pow t1.getNumericalValue? t2.getNumericalValue?
  | _ => none

/-- If the tree corresponds to a variable or parameter, return its name. -/
def getIdentifier? (vars : List String) : EggTree → Option String
  | Tree.node "var" #[Tree.leaf s] => if s ∈ vars then some s else none
  | Tree.node "param" #[Tree.leaf s] => if s ∈ vars then some s else none
  | _ => none

/-- Flatten an `EggTree` to a string to send to egg. -/
partial def toEggString : EggTree → String
  | Tree.node n children =>
    let childrenStr := (children.map EggTree.toEggString).data
    "(" ++ n ++ " " ++ (" ".intercalate childrenStr) ++ ")"
  | Tree.leaf n => n

/-- Size of the expresison's AST that an `EggTree` encodes.. -/
partial def size : EggTree → Nat
  | Tree.node "var" _ => 1
  | Tree.node _ children => 1 + (children.map size).foldl Nat.add 0
  | Tree.leaf _ => 1

/-- Compose the components of an `EggOCTree` into a single `EggTree`. -/
def ofEggOCTree (ocTree : EggOCTree) : EggTree :=
  let objFun := ocTree.objFun.2
  let constrs := ocTree.constr.map
    fun (h, c) => Tree.node "constr" #[Tree.leaf h, c]
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constrs" constrs
  Tree.node "prob" #[objFunNode, constrNode]

end EggTree

namespace EggOCTreeExtended

/-- Helper function for `fromComponents` that processes a single domain-defining expression. -/
def processDomainExprTree (h : String) (c : Tree String String) (vars : List String) :
    Option EggDomainIdentified :=
  -- Detect domain constraints. We capture the following cases:
  -- * x ≤ f and f ≤ x,
  -- * x < f and f < x,
  -- * x = f and f = x,
  -- where "x" is a variable name and "f" is a numerical value.
  match c with
  | Tree.node "le" #[(tl : EggTree), (tr : EggTree)] =>
      match (tl.getIdentifier? vars, tr.getNumericalValue?) with
      -- v ∈ (-inf, f]
      | (some v, some f) => some ⟨h, v, ⟨"-inf", f.toString, "1", "0"⟩⟩
      | _ =>
        match (tl.getNumericalValue?, tr.getIdentifier? vars) with
        -- v ∈ [f, inf)
        | (some f, some v) => some ⟨h, v, ⟨f.toString, "inf", "0", "1"⟩⟩
        | _ => none
  | Tree.node "lt" #[(tl : EggTree), (tr : EggTree)] =>
      match (tl.getIdentifier? vars, tr.getNumericalValue?) with
      -- v ∈ (-inf, f)
      | (some v, some f) => some ⟨h, v, ⟨"-inf", f.toString, "1", "1"⟩⟩
      | _ =>
        match (tl.getNumericalValue?, tr.getIdentifier? vars) with
        -- v ∈ (f, inf)
        | (some f, some v) => some ⟨h, v, ⟨f.toString, "inf", "1", "1"⟩⟩
        | _ => none
  | Tree.node "eq" #[(tl : EggTree), (tr : EggTree)] =>
      match (tl.getIdentifier? vars, tr.getNumericalValue?) with
      -- v ∈ [f, f]
      | (some v, some f) => some ⟨h, v, ⟨f.toString, f.toString, "0", "0"⟩⟩
      | _ =>
        match (tl.getNumericalValue?, tr.getIdentifier? vars) with
        -- v ∈ [f, f]
        | (some f, some v) => some ⟨h, v, ⟨f.toString, f.toString, "0", "0"⟩⟩
        | _ => none
  | _ => none

/-- Given an expression representing a minimization problem, turn it into a tree of strings, also
extract all the domain information from simple constraints. Adjust operations to match the names
of the constructors in the `egg` language. -/
def fromComponents (objFun : String × EggTree) (constr : Array (String × EggTree))
    (vars : List String) : MetaM EggOCTreeExtended := do
  let mut domainConstrs := #[]
  let mut i := 0
  for (h, c) in constr do
    -- NOTE: some constraints may have the same name, so we add the index.
    let h := s!"{i}:" ++ h
    match processDomainExprTree h c vars with
    | some r => domainConstrs := domainConstrs.push r
    | none => pure ()
    i := i + 1

  -- Surround variables and adjust operations in the whole tree.
  let ocTree : OC (String × EggTree) := {
    objFun := (objFun.1, ← EggTree.adjustOps objFun.2)
    constr := ← constr.mapIdxM <|
      -- NOTE: some constraints may have the same name, so we add the index.
      fun i (h, c) => return (s!"{i}:" ++ h, ← EggTree.adjustOps c) }
  return (ocTree, domainConstrs)

/-- Get the atom tree form a minimization problem. Then call `fromComponents`, which takes care of
adjusting all nodes and extracting the domain information from the constraints. -/
def fromMinimization (e : MinimizationExpr) (vars : List String) :
    MetaM EggOCTreeExtended := do
  let ocTree ← UncheckedDCP.uncheckedTreeFromMinimizationExpr e
  fromComponents ocTree.objFun ocTree.constr vars

end EggOCTreeExtended

namespace EggMinimization

/-- Convert `EggOCTree `EggMinimization` by flattening all trees. -/
def ofEggOCTree (oc : EggOCTree) : EggMinimization :=
  { objFun := EggTree.toEggString oc.objFun.2,
    constrs := Array.data <| oc.constr.map fun (h, c) => (h, EggTree.toEggString c) }

end EggMinimization

end CvxLean
