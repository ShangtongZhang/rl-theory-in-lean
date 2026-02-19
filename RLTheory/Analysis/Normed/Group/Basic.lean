/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic

variable {E : Type*} [SeminormedAddGroup E]

lemma norm_add_sq_le_norm_sq_add_norm_sq (x y : E) :
  ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := add_sq_le
  calc ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := sq_le_sq' (by linarith [norm_nonneg (x + y)]) h1
    _ ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := h2
    _ = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by ring
