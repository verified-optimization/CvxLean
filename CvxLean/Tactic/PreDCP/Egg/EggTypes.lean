import Lean
import CvxLean.Tactic.DCP.Tree
import CvxLean.Tactic.DCP.OC

/-!
The main types user around the `egg` interface.
-/

namespace CvxLean

section Minimization

/-- An intermediate structure to represent problems as trees of strings. -/
def EggTree := Tree String String

instance : Inhabited EggTree where
  default := Tree.leaf ""

/-- A more refined `EggTree`, split by its objective function and components. -/
def EggOCTree := OC (String × EggTree)

/-- Helper structure to keep track of the arguments, some of which may be pre-determined, when
translating from atom trees to trees with constructors in the `egg` language. -/
inductive EggTreeOpArgTag
  | arg
  | val (s : String)

/-- Once `EggTree` is flattened into S-expressions, it can be turned into an `EggMinimization`. This
is what will by JSONified and sent to `egg`. It is split into objective functions and constraints,
with their tag. Note that `egg` builds one problem term from this. However, it is useful to keep
track of the names of the components so that when `egg` comes back with a sequence of rewrites it
can easily indicate the location of the rewrite. -/
structure EggMinimization where
  objFun : String
  constrs : List (String × String)

/-- This encodes an interval, used for e-class analysis. For example `⟨"0", "1", "-inf", "8"⟩`
is how the interval `(-∞, 8]` would be encoded. -/
structure EggDomain where
  hi : String
  lo : String
  hi_open : String
  lo_open : String

/-- Every `EggDomain` is infered from a constraint named `constraintName`, and it corresponds to
a variable or parameter named `varOrParamName`. This structure keeps track of that. -/
structure EggDomainIdentified where
  constraintName : String
  varOrParamName : String
  domain : EggDomain

/-- An `EggOCTree` with also the domain information. -/
def EggOCTreeExtended := EggOCTree × Array EggDomainIdentified

/-- A request consists of an `EggMinimization` and a list of domains per variable (or parameter). -/
structure EggRequest where
  probName : String
  domains : List (String × EggDomain)
  target : EggMinimization

end Minimization

section Rewrites

/-- Recall that, in `egg`, rewrites can be forward or backward (in the response). -/
inductive EggRewriteDirection where
  | Forward
  | Backward
deriving Inhabited, DecidableEq

/-- A rewrite returned by `egg`. -/
structure EggRewrite where
  /-- This is the name of the lemma used for rewriting. -/
  rewriteName : String
  /-- Forward or backward. -/
  direction : EggRewriteDirection
  /-- The name of the constraint or `"objFun"`. -/
  location : String
  /-- Source sub-expression. -/
  subexprFrom : String
  /-- Target sub-expression. -/
  subexprTo : String
  /-- The context expression with a `"?"` in place of the sub-expression. For example, if we are
  rewriting `x + (y + z)` into `x + (z + y)`, the expected term would be `x + ?`, with `subexprFrom`
  set to `y + z` and `subexprTo` set to `z + y`. -/
  expectedTerm : String

end Rewrites

end CvxLean
