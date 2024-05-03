import Lean
import CvxLean.Lib.Minimization
import CvxLean.Lib.Equivalence
import CvxLean.Meta.Minimization
import CvxLean.Meta.Util.Expr
import CvxLean.Meta.Util.Error
import CvxLean.Meta.TacticBuilder
import CvxLean.Tactic.Arith.Arith
import CvxLean.Tactic.Basic.RemoveTrivialConstrs
import CvxLean.Tactic.Basic.ConvOpt

/-!
# Change of variables

This file defines the `change_of_variables` tactic.  The idea is that change of variable functions
are registered as instances of the `ChangeOfVariables` typeclass. These instances are also currently
defined in this file. The tactic takes care of renaming the variables as needed, finding the change
of variables, and proving the condition.

We illustrate it with an example of how to use it inside the `equivalence` command:
```
equivalence eqv/q :
    optimization (x : ℝ)
      minimize x
      subject to
        c : 0 < x := by
  change_of_variables (u) (x ↦ exp u)
```
The resulting problem `q` looks as follows:
```
optimization (u : ℝ)
  minimize exp u
  subject to
    c : 0 < exp u
```
We provide `change_of_variables!` as a convenient variant that also tries to remove trivial
constraints. In this case, it would remove `0 < exp u` as it is always true.
-/

namespace CvxLean

open Minimization

/-- Change of variables functions are registered using this typeclass. The only requirement
(`property`) is that they have a right inverse `inv` over some domain given by `condition`. -/
class ChangeOfVariables {D E} (c : E → D) where
  inv : D → E
  condition : D → Prop
  property : ∀ x, condition x → c (inv x) = x

/-- A change of variables is an equivalence-preserving transformation, as long as the condition
holds in the feasible set. -/
@[equiv]
def ChangeOfVariables.toEquivalence {D E R} [Preorder R] {f : D → R} {cs : D → Prop} (c : E → D)
    [cov : ChangeOfVariables c] (h : ∀ x, cs x → cov.condition x) :
    ⟨f, cs⟩ ≡ ⟨fun x => f (c x), fun x => cs (c x)⟩ :=
  Equivalence.ofStrongEquivalence <|
  { phi := fun x => cov.inv x
    psi := fun y => c y
    phi_feasibility := fun x hx => by simp [feasible, cov.property x (h x hx)]; exact hx
    psi_feasibility := fun y hy => hy
    phi_optimality := fun x hx => by simp [cov.property x (h x hx)]
    psi_optimality := fun y _ => by simp }

section Structural

/-- Composing changes of variables results in a valid change of variables. -/
instance ChangeOfVariables.comp {D E F} (c₁ : E → D) (c₂ : F → E) [cov₁ : ChangeOfVariables c₁]
    [cov₂ : ChangeOfVariables c₂] : ChangeOfVariables (c₁ ∘ c₂) :=
  { inv := cov₂.inv ∘ cov₁.inv
    condition := fun x => cov₁.condition x ∧ cov₂.condition (cov₁.inv x)
    property := fun x ⟨hx₁, hx₂⟩ => by simp [cov₂.property (cov₁.inv x) hx₂, cov₁.property x hx₁] }

/-- Apply change of variables to the left of a product domain. -/
instance ChangeOfVariables.prod_left {D E F} (c : E → D) [cov : ChangeOfVariables c] :
    ChangeOfVariables (fun x : E × F => (c x.1, x.2)) :=
  { inv := fun ⟨x₁, x₂⟩ => (cov.inv x₁, x₂)
    condition := fun ⟨x₁, _⟩ => cov.condition x₁
    property := fun ⟨x₁, x₂⟩ hx => by simp [cov.property x₁ hx] }

/-- Apply change of variables to the right of a product domain. -/
instance ChangeOfVariables.prod_right {D E F} (c : E → D) [cov : ChangeOfVariables c] :
    ChangeOfVariables (fun x : F × E => (x.1, c x.2)) :=
  { inv := fun ⟨x₁, x₂⟩ => (x₁, cov.inv x₂)
    condition := fun ⟨_, x₂⟩ => cov.condition x₂
    property := fun ⟨x₁, x₂⟩ hx => by simp [cov.property x₂ hx] }

/-- The identity map is a valid change of variables. -/
instance ChangeOfVariables.id {D} : ChangeOfVariables (fun x : D => x) :=
  { inv := fun x => x
    condition := fun _ => True
    property := fun _ _ => rfl }

end Structural

noncomputable section RealInstances

open Real

instance : ChangeOfVariables exp :=
  { inv := log
    condition := fun x => 0 < x
    property := fun _ hx => exp_log hx }

instance : ChangeOfVariables sqrt :=
  { inv := (fun x => x ^ 2)
    condition := fun x => 0 ≤ x
    property := fun _ hx => sqrt_sq hx }

instance : ChangeOfVariables (fun x : ℝ => x⁻¹) :=
  { inv := fun x => x⁻¹
    -- NOTE: x ≠ 0 is technically not necessary as `0⁻¹⁻¹ = 0`, but we want to explicitly always
    -- avoid division by zero.
    condition := fun x => x ≠ 0
    property := fun x _ => by field_simp }

instance {a : ℝ} : ChangeOfVariables (fun x : ℝ => a * x) :=
  { inv := fun x => (1 / a) * x
    condition := fun _ => a ≠ 0
    property := fun _ h => by rw [← mul_assoc, mul_one_div, div_self h, one_mul] }

instance {a : ℝ} : ChangeOfVariables (fun x : ℝ => a / x) :=
  { inv := fun x => a / x
    condition := fun x => x ≠ 0 ∧ a ≠ 0
    property := fun _ ⟨_, ha⟩ => by field_simp }

instance {a : ℝ} : ChangeOfVariables (fun x : ℝ => x + a) :=
  { inv := fun x => x - a
    condition := fun _ => True
    property := fun _ _ => by ring }

instance {a : ℕ} : ChangeOfVariables (fun x : ℝ => x + a) :=
  { inv := fun x => x - a
    condition := fun _ => True
    property := fun _ _ => by ring }

end RealInstances

noncomputable section VecInstances

instance {n : ℕ} {a : Fin n → ℝ} : ChangeOfVariables (fun (v : Fin n → ℝ) => a / v) :=
  { inv := fun v => a / v
    condition := fun v => ∀ i, v i ≠ 0 ∧ a i ≠ 0
    property := fun v hnot0 => by
      ext i
      simp [← div_mul, div_self (hnot0 i).2, one_mul] }

end VecInstances

open Lean Elab Meta Tactic Term

namespace Meta

/-- This defines the tactic `change_of_variables (u) (x ↦ exp u)`. It follows the following steps:
1. Detect exactly where to apply the change of variables.
2. Syntesize the instance.
2. Prove the conditions.
3. Apply the change of variables to equivalence theorem.

For now, it only works with real variables.-/
def changeOfVariablesBuilder (newVarStx varToChangeStx : TSyntax `ident)
    (changeStx : TSyntax `term) : EquivalenceBuilder Unit :=
  fun eqvExpr g => g.withContext do
    let newVar := newVarStx.getId
    let varToChange := varToChangeStx.getId

    let lhsMinExpr ← eqvExpr.toMinimizationExprLHS
    let vars ← decomposeDomain (← instantiateMVars lhsMinExpr.domain)

    -- Find change of variables location.
    let covIdx := vars.findIdx? (fun ⟨n, _⟩ => n == varToChange)
    if covIdx.isNone then
      throwChangeOfVariablesError "variable {varToChange} not found in domain."
    let covIdx := covIdx.get!

    -- New domain.
    let newVars := vars.map (fun ⟨n, ty⟩ => ⟨if n = varToChange then newVar else n, ty⟩)
    let newDomain := composeDomain newVars

    -- Construct change of variables function.
    let fvars := Array.mk <| vars.map (fun ⟨n, _⟩ => mkFVar (FVarId.mk n))
    -- u ↦ c(u)
    let changeFnStx ← `(fun ($newVarStx : ℝ) => $changeStx)
    let changeFn ← Tactic.elabTerm changeFnStx none
    -- c(x)
    let changeTerm ← Core.betaReduce <|
      mkApp changeFn (mkFVar (FVarId.mk varToChange))
    -- (x₁, ..., u, ..., xₙ) ↦ (x₁, ..., c(u), ..., xₙ)
    let c ← withLocalDeclD `p newDomain fun p => do
      Meta.withDomainLocalDecls newDomain p fun xs prs => do
        -- (x₁, ..., c(xᵢ), ..., xₙ)
        let fullChangeTerm ← Expr.mkProd <|
          (xs.take covIdx) ++ #[changeTerm] ++ (xs.drop (covIdx + 1))
        let replacedFVars := Expr.replaceFVars fullChangeTerm fvars xs
        mkLambdaFVars #[p] (Expr.replaceFVars replacedFVars xs prs)

    -- Make `ChangeOfVariables` instance.
    -- The arguments are the number of variables to the left and right  of `varToChange`.
    let rec mkCovExpr : ℕ → ℕ → MetaM Expr
      | 0, 0 => do synthInstance (← mkAppM ``ChangeOfVariables #[changeFn])
      | 0, _ => do
          let rType := composeDomain (newVars.drop (covIdx + 1))
          mkAppOptM ``ChangeOfVariables.prod_left #[none, none, rType, changeFn, none]
      | l + 1, r => do
          let covExpr' ← mkCovExpr l r
          mkAppOptM ``ChangeOfVariables.prod_right #[none, none, mkConst ``Real, none, covExpr']
    let covExpr ← mkCovExpr covIdx (vars.length - covIdx - 1)

    -- Apply `ChangeOfVariables.toEquivalence`.
    let D := lhsMinExpr.domain
    let E := newDomain
    let R := lhsMinExpr.codomain
    let RPreorder ← synthInstance (mkAppN (mkConst ``Preorder [levelZero]) #[R])
    let f := lhsMinExpr.objFun
    let cs := lhsMinExpr.constraints
    let toApply := mkAppN (mkConst ``ChangeOfVariables.toEquivalence)
      #[D, E, R, RPreorder, f, cs, c, covExpr]
    let toApply ← instantiateMVars toApply
    let gsAfterApply ← g.apply toApply
    if gsAfterApply.length != 1 then
      throwChangeOfVariablesError (
        "failed to apply `ChangeOfVariables.toEquivalence`, " ++
        "make sure that the change of variables is inferrable by type class resolution.")

    -- Solve change of variables condition.
    let gCondition := gsAfterApply[0]!
    let (_, gCondition) ← gCondition.introN 2 [`x, `h]
    let gsFinal ← evalTacticAt
      (← `(tactic| (simp [ChangeOfVariables.condition] at * <;> arith))) gCondition
    if gsFinal.length != 0 then
      trace[CvxLean.debug] "Could not prove {gsFinal}."
      throwChangeOfVariablesError "failed to solve change of variables condition."

end Meta

namespace Tactic

syntax (name := changeOfVariables)
  "change_of_variables" "(" ident ")" "(" ident "↦" term ")" : tactic

@[tactic changeOfVariables]
def evalChangeOfVariables : Tactic := fun stx => match stx with
  | `(tactic| change_of_variables ($newVarStx) ($varToChangeStx ↦ $changeStx)) => do
      (changeOfVariablesBuilder newVarStx varToChangeStx changeStx).toTactic
      evalTactic <| ← `(tactic| conv_opt => norm_num1)
      saveTacticInfoForToken stx
  | _ => throwUnsupportedSyntax

/-- Tries to remove trivial constraints after applying the change of variables. -/
syntax (name := changeOfVariablesAndRemove)
  "change_of_variables!" "(" ident ")" "(" ident "↦" term ")" : tactic

macro_rules
  | `(tactic| change_of_variables! ($newVarStx) ($varToChangeStx ↦ $changeStx)) =>
    `(tactic|
        change_of_variables ($newVarStx) ($varToChangeStx ↦ $changeStx);
        remove_trivial_constrs)

end Tactic

end CvxLean
