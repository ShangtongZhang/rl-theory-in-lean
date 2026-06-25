/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Data.Real.Basic

open Finset Real

namespace Matrix

variable {m n β: Type*} [Fintype m]

lemma sum_vecMul {s : Finset β} (f : β → (m → ℝ)) (A : Matrix m n ℝ)
  : (∑ x ∈ s, f x) ᵥ* A = ∑ x ∈ s, (f x) ᵥ* A := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma vecMul_smul' (v : m → ℝ) (c : ℝ) (A : Matrix m n ℝ) :
  v ᵥ* (c • A) = c • (v ᵥ* A) := by
  funext j
  simp [Matrix.vecMul, Matrix.smul_apply, dotProduct, Finset.mul_sum, mul_left_comm]

lemma smul_vecMul (c : ℝ) (v : m → ℝ) (A : Matrix m n ℝ) :
  (c • v) ᵥ* A = c • (v ᵥ* A) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

omit [Fintype m] in
lemma mul_diagonal_mulVec
  [DecidableEq n] [Fintype n] (d : n → ℝ) (x : n → ℝ) (A : Matrix m n ℝ) :
  (A * Matrix.diagonal d) *ᵥ x = ∑ i, d i • x i • A.col i := by
  ext j
  simp [mul_diagonal, mulVec, dotProduct]
  apply sum_congr rfl
  intro i hi
  ring_nf

omit [Fintype m] in
lemma mulVec_apply [Fintype n]
  (A : Matrix m n ℝ) (x : n → ℝ) (j : m) :
  (A *ᵥ x) j = ∑ i, A j i * x i := by
  simp [mulVec, dotProduct]

section square

variable {A : Matrix m m ℝ}

lemma dotProduct_transpose_mulVec (x y : m → ℝ) :
   x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  nth_rw 1 [dotProduct_mulVec]
  rw [dotProduct_comm]
  rw [vecMul_transpose]

lemma vecMul_diagonal_dotProduct
  [DecidableEq m] (d x y: m → ℝ) :
  x ᵥ* Matrix.diagonal d ⬝ᵥ y = ∑ i, d i * x i * y i := by
  simp [dotProduct, Matrix.vecMul, Matrix.diagonal]
  apply sum_congr rfl
  ring_nf
  simp

end square

end Matrix
