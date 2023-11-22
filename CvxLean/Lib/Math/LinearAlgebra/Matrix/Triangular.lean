/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Matrix.Block

import CvxLean.Lib.Math.LinearAlgebra.Matrix.Block

/-
# Triangular Matrices
This file defines upper and lower triangular matrices. The definitions are based on
`Matrix.BlockTriangular`. All properties should ideally be proved for `Matrix.BlockTriangular` in
general and then specialized to (nonblock)-triangular matrices here.
-/

namespace Matrix

open BigOperators
open Matrix

variable {α m n : Type _}
variable {R : Type _} [CommRing R] {M N : Matrix m m R}

/-- An upper triangular matrix is a matrix whose entries are zero below the diagonal. -/
def upperTriangular [LT m] (M : Matrix m m R) :=
  M.BlockTriangular id

/-- A lower triangular matrix is a matrix whose entries are zero above the diagonal. -/
def lowerTriangular [LT m] (M : Matrix m m R) :=
  M.BlockTriangular OrderDual.toDual

/-- The inverse of an upper triangular matrix is upper triangular -/
lemma upperTriangular_inv_of_upperTriangular [Fintype m] [LinearOrder m] [Invertible M]
  (hM : upperTriangular M) : upperTriangular M⁻¹ :=
blockTriangular_inv_of_blockTriangular hM

/-- The inverse of a lower triangular matrix is lower triangular -/
lemma lowerTriangular_inv_of_lowerTriangular [Fintype m] [LinearOrder m] [Invertible M]
  (hM : lowerTriangular M) : lowerTriangular M⁻¹ :=
blockTriangular_inv_of_blockTriangular hM

/-- Multiplication of upper triangular matrices is upper triangular -/
lemma upperTriangular.mul [Fintype m] [LinearOrder m]
  (hM : upperTriangular M) (hN : upperTriangular N) : upperTriangular (M * N) :=
BlockTriangular.mul hM hN

/-- Multiplication of lower triangular matrices is lower triangular -/
lemma lowerTriangular.mul [Fintype m] [LinearOrder m]
  (hM : lowerTriangular M) (hN : lowerTriangular N) : lowerTriangular (M * N) :=
BlockTriangular.mul hM hN

/-- Transpose of lower triangular matrix is upper triangular -/
lemma lowerTriangular.transpose [Fintype m] [LinearOrder m]
  (hM : lowerTriangular M) : upperTriangular Mᵀ :=
BlockTriangular.transpose hM

/-- Transpose of upper triangular matrix is lower triangular -/
lemma upperTriangular.transpose [Fintype m] [LinearOrder m]
  (hM : upperTriangular M) : lowerTriangular Mᵀ :=
BlockTriangular.transpose hM

lemma diag_inv_mul_diag_eq_one_of_upperTriangular [Fintype m] [LinearOrder m] [Invertible M]
  (hM : upperTriangular M) (k : m) : M⁻¹ k k * M k k = 1 := by
  letI : Unique {a // id a = k} := ⟨⟨⟨k, rfl⟩⟩, fun j => Subtype.ext j.property⟩;
  have h := congr_fun (congr_fun (toSquareBlock_inv_mul_toSquareBlock_eq_one hM k) ⟨k, rfl⟩) ⟨k, rfl⟩
  dsimp only [HMul.hMul, dotProduct] at h
  rw [@Fintype.sum_unique _ _ _ _] at h
  simp at h; rw [←h]; simp [toSquareBlock, toSquareBlockProp]; rfl

lemma diag_inv_mul_diag_eq_one_of_lowerTriangular [Fintype m] [LinearOrder m] [Invertible M]
  (hM : lowerTriangular M) (k : m) : M⁻¹ k k * M k k = 1 := by
  letI : Unique {a // OrderDual.toDual a = k} := ⟨⟨⟨k, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  have h := congr_fun (congr_fun (toSquareBlock_inv_mul_toSquareBlock_eq_one hM k) ⟨k, rfl⟩) ⟨k, rfl⟩
  dsimp [HMul.hMul, dotProduct] at h
  rw [@Fintype.sum_unique _ _ _ this] at h
  simp at h; rw [←h]; simp [toSquareBlock, toSquareBlockProp]; rfl

end Matrix
