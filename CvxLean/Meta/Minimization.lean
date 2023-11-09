import CvxLean.Syntax.Label
import CvxLean.Meta.Missing.Meta

namespace CvxLean

namespace Meta

open Lean Lean.Meta

variable [MonadControlT MetaM m] [Monad m]


/-- Structure holding all the components in the `Minimization` type. -/
structure MinimizationExpr where
  domain : Expr
  codomain : Expr
  objFun : Expr
  constraints : Expr

namespace MinimizationExpr

/-- Build a `Minimization` type from `MinimizationExpr`. -/
def toExpr (minExpr : MinimizationExpr) : Expr :=
  mkApp4 (mkConst `Minimization.mk)
    minExpr.domain minExpr.codomain minExpr.objFun minExpr.constraints

/-- Decompose `Minimization` type into its components. -/
def fromExpr (prob : Expr) : MetaM MinimizationExpr :=
  match prob with
  | .app (.app (.app (.app (.const `Minimization.mk _)
      domain) codomain) objFun) constraints => do
    return MinimizationExpr.mk domain codomain objFun constraints
  | _ => throwError "Expr not of the form `Minimization.mk ...`."

end MinimizationExpr

/-- Structure holding all the components in the `Solution` type. -/
structure SolutionExpr where
  domain : Expr
  codomain : Expr
  codomainPreorder : Expr
  domain' : Expr
  codomain' : Expr
  objFun : Expr
  constraints : Expr

namespace SolutionExpr

/-- Build `MinimizationExpr` from `SolutionExpr`. -/
def toMinimizationExpr (solExpr : SolutionExpr) : MinimizationExpr :=
  { domain := solExpr.domain'
    codomain := solExpr.codomain'
    objFun := solExpr.objFun
    constraints := solExpr.constraints }

/-- Build a `Solution` type from `SolutionExpr`. -/
def toExpr (solExpr : SolutionExpr) : Expr :=
  mkApp4 (mkConst `Minimization.Solution)
    solExpr.domain solExpr.codomain solExpr.codomainPreorder
    (solExpr.toMinimizationExpr.toExpr)

/-- Decompose `Solution` type into its components. -/
def fromExpr (goalType : Expr) : MetaM SolutionExpr := do
  match goalType with
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.const `Minimization.Solution _ )
        domain) codomain) codomainPreorder)
          (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const `Minimization.mk _)
            domain') codomain') objFun) constraints) => do
    return SolutionExpr.mk domain codomain codomainPreorder
      domain' codomain' objFun constraints
  | _ => throwError "Goal not of the form `Minimization.Solution ...`."

/-- Applies `SolutionExpr.fromExpr` to goal. -/
def fromGoal (goal : MVarId) : MetaM SolutionExpr := do
  let goalType ← whnf (← MVarId.getDecl goal).type
  fromExpr goalType

end SolutionExpr

/-- Helper function used in to read the goal handling the `reduction` and
`equivalence` cases. -/
def getExprRawFromGoal (isEquiv : Bool) (e : Expr) : MetaM Expr := do
  if isEquiv then
    if e.isAppOf `Minimization.Equivalence then
      -- NOTE(RFM): Equivalence 0:R 1:D 2:E 3:RPreorder 4:p 5:q
      let lhs := e.getArg! 4
      return lhs
    else
      throwError "convexify expected an equivalence, got {e}."
  else
    if e.isAppOf `Minimization.Solution then
      -- Get `p` From `Solution p`.
      return e.getArg! 3
    else
      throwError "convexify expected an Expr of the form `Solution ...`."

/-- Replaces projections of an FVar `p` in an expression `e` by the expressions `rs`.
  For example, `p.2.2.1` will be replaced by `rs[2]`. If `p` is not fully projected,
  e.g. `p.2` when `rs` has more than 2 elements, it is not replaced at all.  -/
def replaceProjections (e : Expr) (p : FVarId) (rs : Array Expr) : MetaM Expr := do
  let pre (e : Expr) : MetaM TransformStep := do
    match ← decomposeProj e p rs.data with
    | some r => return TransformStep.done r
    | none => return TransformStep.continue
  transform e (pre := pre)
where
  decomposeProj (e : Expr) (p : FVarId) (rs : List Expr) (first : Option Bool := none) :
      MetaM (Option Expr) := do
    /- `first` tells us whether the outermost projection was `.1` (`some true`) or
       `.2` (`some false`). If this is not a recursive call, `first` is `none`. -/
    match first, e, rs with
    | _, Expr.fvar fVarId, [r] =>
      if fVarId == p then return r else return none
    | some true, Expr.fvar fVarId, r :: _ :: _ =>
      if fVarId == p then return r else return none
    | none, Expr.app (Expr.app (Expr.app (Expr.const ``Prod.fst _) _) _) e, r :: rs => do
      return ← decomposeProj e p (r :: rs) (first := true)
    | _, Expr.app (Expr.app (Expr.app (Expr.const ``Prod.snd _) _) _) e, _ :: rs => do
      return ← decomposeProj e p rs (first := first == some true)
    | _, _, [] => return none
    | _, _, _ :: _ => return none

/-- Determine a list of variables described by a `domain`.
  Returns a list of variables, consisting of their name and type. -/
def decomposeDomain (domain : Expr) : m (List (Name × Expr)) := do
  match domain with
  | Expr.app (Expr.app (Expr.const `Prod _) ty1) ty2 => do
    return (← decomposeLabel ty1) :: (← decomposeDomain ty2)
  | _ => do return [← decomposeLabel domain]

/-- Get a HashSet of variable names in a given domain -/
def getVariableNameSet (domain : Expr) : m (HashSet Name) := do
  let mut res : HashSet Name := {}
  for (name, _) in ← decomposeDomain domain do
    res := res.insert name
  return res

/-- Determine domain type from a list of variables and their types. -/
def composeDomain (vars : List (Name × Expr)) : Expr :=
  match vars with
  | [] => mkConst `Unit
  | [(name, ty)] => mkLabel name ty
  | (name, ty) :: rest =>
    mkApp2 (mkConst `Prod [levelZero, levelZero])
      (mkLabel name ty) (composeDomain rest)

/-- Determine a list of variables described by a `domain`.
  The expression `p` must be a variable of Type `domain`.
  Returns a list of variables, with name, type, and definition in terms of `p` -/
partial def mkProjections (domain : Expr) (p : Expr) : m (List (Name × Expr × Expr)) := do
  match domain with
  | Expr.app (Expr.app (Expr.const `Prod lvls) (ty1 : Expr)) (ty2 : Expr) => do
    let v ← getLabelName ty1
    let d := mkApp3 (mkConst `Prod.fst lvls) ty1 ty2 p
    let r ← mkProjections ty2 (mkApp3 (mkConst `Prod.snd lvls) ty1 ty2 p)
    return (v, ty1, d) :: r
  | _ => do return [(← getLabelName domain, domain, p)]

/-- Introduce let declarations into the context, corresponding to the projections of `p`.
    The argument `domain` specifies the type of `p`. CvxLeanLabels in the `domain` are used to
    determine the names of the new variables. -/
def withDomainLocalDecls [Inhabited α] (domain : Expr) (p : Expr)
    (x : Array Expr → Array Expr → m α) : m α  := do
  let pr := (← mkProjections domain p).toArray
  withLetDecls' (pr.map fun (n, ty, val) => (n, fun _ => return ty, fun _ => return val)) fun xs => do
    let mut xs := xs
    -- Use projections instead of variables named "_" :
    for i in [:pr.size] do
      if pr[i]!.1 == `_ then
        xs := xs.set! i pr[i]!.2.2
    x xs (pr.map (fun a => a.2.2))

/-- Decompose an expression into its `And`-connected components -/
def decomposeAnd (e : Expr) : MetaM (List (Expr)) := do
  match e with
  | Expr.app (Expr.app (Expr.const ``And _) p) q => do
    return p :: (← decomposeAnd q)
  | _ => return [e]

/-- Decompose an expression of `And`-connected constraints into a list of names and expressions. -/
def decomposeConstraints (e : Expr) : MetaM (List (Name × Expr)) := do
  (← decomposeAnd e).mapM fun e => do
    return (← getLabelName e, e)

/-- Get a HashSet of constraint names in a given domain -/
def getConstraintNameSet (e : Expr) : MetaM (HashSet Name) := do
  let mut res : HashSet Name := {}
  for (name, _) in ← decomposeConstraints e do
    res := res.insert name
  return res

/-- Compose a list of expressions with `And` -/
def composeAnd : List Expr → Expr
  | [] => mkConst ``True
  | [c] => c
  | c :: cs => mkApp2 (mkConst ``And) c (composeAnd cs)

/-- Compose a list of expressions with `And` -/
def composeAndWithProj : List Expr → (Expr × (Expr → List Expr))
  | [] => (mkConst ``True, fun _ => [])
  | [c] => (c, fun e => [e])
  | c :: cs =>
    let (cs, prs) := composeAndWithProj cs
    let res := mkApp2 (mkConst ``And) c cs
    let prs := fun e => mkApp3 (mkConst ``And.left) c cs e
                    :: prs (mkApp3 (mkConst ``And.right) c cs e)
    (res, prs)

/-- Generates a name that is not yet contained in `set` -/
partial def generateNewName (base : String) (set : HashSet Name) : MetaM Name := do
  tryNumber 1 set
where
  tryNumber (i : Nat) vars : MetaM Name := do
    let name := s!"{base}{i}"
    if vars.contains name
    then tryNumber (i+1) vars
    else return name

end Meta

end CvxLean
