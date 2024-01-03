import Mathlib.Data.Real.Basic
import CvxLean.Lib.Math.LinearAlgebra.Matrix.Triangular

namespace Matrix

/-!
# Conversion to upper triangular matrices

Defines `toUpperTri` and proves some basic lemmas about it.
-/

open Matrix

variable {n : Type} [Fintype n] [LinearOrder n] [LocallyFiniteOrderBot n]

def toUpperTri {m α : Type _} [LinearOrder m] [Zero α] (A : Matrix m m α) :
  Matrix m m α :=
  fun i j => if i ≤ j then A i j else 0

theorem toUpperTri_zero {m : Type _} [LinearOrder m] :
  Matrix.toUpperTri (0 : Matrix m m ℝ) = 0 := by
  funext i j ; simp [Matrix.toUpperTri]

theorem toUpperTri_smul {m : Type _} [LinearOrder m]
  (A : Matrix m m ℝ) (κ : ℝ) :
  κ • Matrix.toUpperTri A = Matrix.toUpperTri (κ • A) := by
  funext i j ; rw [Pi.smul_apply, Pi.smul_apply] ; simp only [Matrix.toUpperTri]
  by_cases h : i ≤ j <;> simp [h]

theorem toUpperTri_add {m : Type _} [LinearOrder m]
  (A B : Matrix m m ℝ) :
  Matrix.toUpperTri (A + B) = Matrix.toUpperTri A + Matrix.toUpperTri B := by
  funext i j ; rw [Pi.add_apply, Pi.add_apply] ; simp only [Matrix.toUpperTri]
  by_cases h : i ≤ j <;> simp [h]

lemma upperTriangular_toUpperTri {m : Type _} [LinearOrder m]
  (A : Matrix m m ℝ) : A.toUpperTri.upperTriangular := by
  intros i j hij
  unfold toUpperTri
  rw [if_neg]
  simpa using hij

lemma upperTriangular.toUpperTri_eq {A : Matrix n n ℝ}
  (hA : upperTriangular A) : A.toUpperTri = A := by
  ext i j
  by_cases h : i ≤ j
  simp [toUpperTri, h]
  simp [toUpperTri, h, hA (lt_of_not_ge h)]

end Matrix
