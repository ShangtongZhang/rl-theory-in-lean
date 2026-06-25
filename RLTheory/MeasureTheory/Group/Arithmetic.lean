/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import RLTheory.Defs

open Real Finset Filter MeasureTheory RLTheory
open scoped MeasureTheory Topology InnerProductSpace RealInnerProductSpace

lemma Measurable.inner
  {α : Type*} [MeasurableSpace α] {d : ℕ}
  {f : α → E d} (hf : Measurable f) {g : α → E d} (hg : Measurable g)
  : Measurable fun a => ⟪f a, g a⟫ := by
    simp
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.mul
    apply measurable_pi_iff.mp
    exact hg
    apply measurable_pi_iff.mp
    exact hf
