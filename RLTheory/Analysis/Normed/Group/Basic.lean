/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.Normed.Group.Basic

import RLTheory.Data.Real.Basic

open Real

variable {E : Type*} [SeminormedAddGroup E]

lemma norm_add_sq_le_norm_sq_add_norm_sq (x y : E) :
  ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  grw [norm_add_le]
  grw [add_sq_le_sq_add_sq]
