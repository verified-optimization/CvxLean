import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Matrix

/-!
More results about block matrices (see `Mathlib.LinearAlgebra.Matrix.Block`).
-/

open Matrix

open Finset

universe v

variable {α β m n o : Type _} {m' n' : α → Type _}
variable {R : Type v} [CommRing R] {M : Matrix m m R} {b : m → α}

section LT

variable [LT α]

lemma BlockTriangular.zero : BlockTriangular (0 : Matrix m m R) b :=
  fun _ _ _ => rfl

end LT

section Preorder

variable [Preorder α]

lemma BlockTriangular_diagonal [DecidableEq m] (d : m → R) :
    BlockTriangular (diagonal d) b :=
  fun _ _ h => diagonal_apply_ne' d (fun h' => ne_of_lt h (congr_arg _ h'))

lemma BlockTriangular_blockDiagonal' [DecidableEq α]
  (d : ∀ (i : α), Matrix (m' i) (m' i) R) :
    BlockTriangular (blockDiagonal'  d) Sigma.fst := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' (fun h' => ne_of_lt h h'.symm)

lemma BlockTriangular_blockDiagonal [DecidableEq α] (d : α → Matrix m m R) :
  BlockTriangular (blockDiagonal d) Prod.snd := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal, BlockTriangular_blockDiagonal']
  exact h

end Preorder

variable [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

lemma toBlock_inverse_mul_toBlock_eq_one_of_BlockTriangular [LinearOrder α]
  [Invertible M] (hM : BlockTriangular M b) (k : α) :
  M⁻¹.toBlock (fun i => b i < k) (fun i => b i < k) *
  M.toBlock (fun i => b i < k) (fun i => b i < k) = 1 := by
  let p := (fun i => b i < k)
  have h_sum : M⁻¹.toBlock p p * M.toBlock p p +
      M⁻¹.toBlock p (fun i => ¬ p i) * M.toBlock (fun i => ¬ p i) p = 1 := by
    rw [←toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_self]
  have h_zero : M.toBlock (fun i => ¬ p i) p = 0
  { ext i j
    simpa using hM (lt_of_lt_of_le j.2 (le_of_not_lt i.2)) }
  simpa [h_zero] using h_sum

/-- The inverse of an upper-left subblock of a block-triangular matrix `M` is
the upper-left subblock of `M⁻¹`. -/
lemma inv_toBlock_of_BlockTriangular [LinearOrder α]
  [Invertible M] (hM : BlockTriangular M b) (k : α) :
  (M.toBlock (fun i => b i < k) (fun i => b i < k))⁻¹ =
  M⁻¹.toBlock (fun i => b i < k) (fun i => b i < k) :=
inv_eq_left_inv (BlockTriangular.toBlock_inverse_mul_toBlock_eq_one hM k)

/-- An upper-left subblock of an invertible block-triangular matrix is
invertible. -/
def invertible_toBlock_of_BlockTriangular
  [LinearOrder α] [Invertible M] (hM : BlockTriangular M b) (k : α) :
  Invertible (M.toBlock (fun i => b i < k) (fun i => b i < k)) :=
invertibleOfLeftInverse _ ((⅟M).toBlock (fun i => b i < k) (fun i => b i < k))
  (by simpa only [invOf_eq_nonsing_inv]
    using BlockTriangular.toBlock_inverse_mul_toBlock_eq_one hM k)

lemma toSquareBlock_inv_mul_toSquareBlock_eq_one [LinearOrder α]
  [Invertible M] (hM : BlockTriangular M b) (k : α) :
  M⁻¹.toSquareBlock b k * M.toSquareBlock b k = 1 := by
  let p := (λ i => b i = k)
  have h_sum : M⁻¹.toBlock p p * M.toBlock p p +
      M⁻¹.toBlock p (λ i => ¬ p i) * M.toBlock (λ i => ¬ p i) p = 1 := by
    rw [←toBlock_mul_eq_add, inv_mul_of_invertible M, toBlock_one_self]
  have h_zero : ∀ i j l,
    M⁻¹.toBlock p (fun i => ¬p i) i j * M.toBlock (fun i => ¬p i) p j l = 0
  { intro i j l
    by_cases hj : b j.1 ≤ k
    { have hj := lt_of_le_of_ne hj j.2
      have hM' := blockTriangular_inv_of_blockTriangular hM
      apply mul_eq_zero_of_left
      simpa using hM' (lt_of_lt_of_eq hj i.2.symm) }
    { have hj := lt_of_not_ge hj
      apply mul_eq_zero_of_right
      simpa using hM (lt_of_eq_of_lt l.2 hj) }}
  have h_zero' :
    M⁻¹.toBlock p (λ (i : m) => ¬p i) * M.toBlock (λ (i : m) => ¬p i) p = 0
  { ext i l
    apply sum_eq_zero (λ j _ => h_zero i j l) }
  simpa [h_zero'] using h_sum

end Matrix
