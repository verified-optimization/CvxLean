import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.PreDCP.UncheckedDCP

section Egg.FromMinimization

open Lean CvxLean

/-- -/
partial def EggTree.toEggString : Tree String String → String
  | Tree.node n children =>
    let childrenStr := (children.map EggTree.toEggString).data
    "(" ++ n ++ " " ++ (" ".intercalate childrenStr) ++ ")"
  | Tree.leaf n => n

/-- -/
def EggTree.ofOCTree (ocTree : OC (String × Tree String String)) :
  Tree String String :=
  let objFun := ocTree.objFun.2
  let constrs := ocTree.constr.map 
    fun (h, c) => Tree.node "constr" #[Tree.leaf h, c]
  let objFunNode := Tree.node "objFun" #[objFun]
  let constrNode := Tree.node "constrs" constrs
  Tree.node "prob" #[objFunNode, constrNode]

partial def EggTree.surroundVars (t : Tree String String) (vars : List String) :=
  match t with
  | Tree.leaf s => if s ∈ vars then Tree.node "var" #[Tree.leaf s] else t
  | Tree.node n children => Tree.node n (children.map (surroundVars · vars))

-- TODO(RFM): Construct this map with commands, not hard-coded. For every key
-- we have the name, the arity and the extra args.
def EggTree.opMap : HashMap String (String × Nat × Array String) :=
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
    ("div",         ("div", 2, #[])),
    ("log",         ("log", 1, #[])),
    ("exp",         ("exp", 1, #[]))
  ]

/-- -/
partial def EggTree.adjustOps (t : Tree String String) :
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

/-- -/
def ExtendedEggTree.fromMinimization (e : Meta.MinimizationExpr) (vars : List String) :
  MetaM (OC (String × Tree String String) × Array (String × String × String)) := do
  let ocTree ← UncheckedDCP.uncheckedTreeFromMinimizationExpr e
  -- Detect domain constraints.
  let nonnegVars := ocTree.constr.filterMap <| fun (h, c) =>
    match c with
    | Tree.node "le" #[Tree.leaf "0", Tree.leaf v] => 
        if v ∈ vars then some (h, v) else none 
    | _ => none
  let posVars := ocTree.constr.filterMap <| fun (h, c) =>
    match c with
    | Tree.node "lt" #[Tree.leaf "0", Tree.leaf v] => 
        if v ∈ vars then some (h, v) else none 
    | _ => none

  let domainConstrs := 
    (nonnegVars.map (fun (h, v) => (h, v, "NonNeg"))) ++ 
    (posVars.map (fun (h, v) => (h, v, "Pos")))

  -- NOTE(RFM): Some empty constraints here coming from '<' conditions?
  -- let ocTree := { ocTree with 
  --   constr := ocTree.constr.filter (fun (_, c) => c.size > 1)}

  -- TODO(RFM): Functions for this.
  let ocTree : OC (String × Tree String String) := { 
    objFun := let (ho, o) := ocTree.objFun; (ho, EggTree.surroundVars o vars)
    constr := ocTree.constr.map (fun (h, c) => (h, EggTree.surroundVars c vars)) }
  let ocTree : OC (String × Tree String String) := {
    objFun := (ocTree.objFun.1, ← EggTree.adjustOps ocTree.objFun.2)
    constr := ← ocTree.constr.mapM (fun (h, c) => return (h, ← EggTree.adjustOps c)) }
  return (ocTree, domainConstrs)

end Egg.FromMinimization
