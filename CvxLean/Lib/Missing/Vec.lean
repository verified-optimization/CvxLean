import CvxLean.Lib.Missing.Real

attribute [-instance] coeDecidableEq

namespace Vec
variable {m : Type u} {n : Type v} [Fintype m] [Fintype n] {α : Type w} (x y : m → α)

instance [HasAbs α] : HasAbs (m → α) := ⟨fun (x : m → α) (i : m) => HasAbs.abs (x i)⟩

def map (f : α → β) (x : m → α) : m → β := 
  fun i => f (x i)

end Vec

@[appUnexpander Matrix.vecEmpty]
def unexpandVecEmpty : Lean.PrettyPrinter.Unexpander := 
fun stx => match stx with
| `(Matrix.vecEmpty) => do return Lean.TSyntax.raw $ ← `(![])
| _ => throw ()

@[appUnexpander Matrix.vecCons]
def unexpandVecCons : Lean.PrettyPrinter.Unexpander := 
fun stx => match stx with
| `(Matrix.vecCons $e ![]) => do return Lean.TSyntax.raw $ ← `(![$e])
| `(Matrix.vecCons $e ![$elem,*]) => do return Lean.TSyntax.raw $ ← `(![$e,$elem,*])
| _ => throw ()

namespace Vec

section Basic
variable {m : Nat} {n : Nat} (x : Finₓ m → α) (y : Finₓ n → α)

/-- Produces a vector containing the first `k` entries of a given vector. -/
def take (k : ℕ) : (Finₓ (LinearOrderₓ.min m k)) → α := fun i => x ⟨i.val, lt_of_lt_of_leₓ i.property (min_le_leftₓ  _ _)⟩

end Basic

noncomputable def supNorm [Fintype n] [HasSupₓ α] [HasAbs α] (x : n → α) := supr fun i => HasAbs.abs (x i)

section AddCommMonoid
variable {α} [AddCommMonoidₓ α] {m : Nat} {n : Nat} (x : Finₓ m → α) (y : Finₓ n → α) 

-- TODO: Why can't I remove `noncomputable`?
noncomputable def sum {m : Type} [Fintype m] (x : m → α) : α := ∑ i, x i

/-- Cumulative sum: The `i`th entry of the `cumsum` vector contains the sum of
  the first `i + 1` elements of the given vector. -/
-- TODO: Why can't I remove `noncomputable`?
noncomputable def cumsum : Finₓ m → α := fun i => ∑ k, (take x (i + 1)) k

end AddCommMonoid

section Semiring
variable [Semiringₓ α] {m : Nat} {n : Nat} (x : Finₓ m → α) (y : Finₓ n → α)

/-- The convolution of `x` and `y` is the vector `z` that `z k = ∑ { x i * y j | i + j = k }`-/
-- TODO: Why can't I remove `noncomputable`?
noncomputable def convolution : Finₓ (m + n - 1) → α := 
  fun k => ∑ (i : Finₓ m), ∑ (j : Finₓ n), if i.val + j.val = k.val then ((x i) * y j) else 0
 
noncomputable def sum_squares : α := Finset.sum Finset.univ fun i => (x i) * x i

end Semiring

section Real

variable {m : Type u} {n : Type v} (x y : m → ℝ)

noncomputable def exp : m → ℝ := 
  fun i => Real.exp (x i)

noncomputable def log : m → ℝ := 
  fun i => Real.log (x i)

noncomputable def entr : m → ℝ := 
  fun i => Real.entr (x i)

noncomputable def huber [Fintype m] (x : m → ℝ) : m → ℝ := 
  fun i => Real.huber (x i)

noncomputable def kl_div : m → ℝ := 
  fun i => Real.kl_div (x i) (y i)

end Real

end Vec
