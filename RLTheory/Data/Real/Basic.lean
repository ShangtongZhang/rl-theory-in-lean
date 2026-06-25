/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real

lemma add_sq_le_sq_add_sq (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  rw [add_sq]
  grw [two_mul_le_add_sq]
  linarith

lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : √x ≤ 1 + x := by
  have : 0 ≤ (√x - 1) ^ 2 := by apply sq_nonneg
  rw [sub_sq] at this
  rw [Real.sq_sqrt hx] at this
  linarith

lemma div_mul_le_of_div_le_div {a b c d : ℝ} (hd : 0 < d)
  (h : a / b ≤ c / d) : a / b * d ≤ c := by
  grw [h]
  rw [div_mul_cancel₀]
  linarith

lemma le_of_le_sub_nonneg {a b c : ℝ} (hc : 0 ≤ c)
  (h : a ≤ b - c) : a ≤ b := by
  linarith

lemma rpow_le_of_le_rpow {a b : ℝ} {r : ℝ}
  (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b)
  (h : a ≤ b ^ r) : a ^ r⁻¹ ≤ b := by
  grw [h]
  rw [←Real.rpow_mul, mul_inv_cancel₀]
  simp
  linarith
  linarith

lemma rpow_neg_le_rpow_neg_of_le {a b : ℝ} {r : ℝ}
  (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
  (h : a ≤ b) : b ^ (-r) ≤ a ^ (-r) := by
  rw [rpow_neg, rpow_neg]
  apply (inv_le_inv₀ ?_ ?_).mpr
  grw [h]
  positivity
  positivity
  positivity
  positivity

lemma div_mul_assoc {a b c : ℝ} :
  a / b * c = a * (c / b) := by
  ring_nf

end Real
