/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open Filter

namespace MeasureTheory
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

lemma integrable_of_norm_le {α : Type*} {β : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] [NormedAddCommGroup β] {f : α → β}
  (hm : AEStronglyMeasurable f μ) (hbdd : ∃ C, ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C)
  : Integrable f μ := by
  obtain ⟨C, hC⟩ := hbdd
  apply integrable_of_norm_sub_le (f₀ := 0) (g := fun ω => C)
  exact hm
  apply integrable_const
  apply integrable_const
  apply Eventually.mono hC
  intro ω hC
  simp
  exact hC

lemma Integrable.finset_sum
  {α ι : Type*} [DecidableEq ι] {m : MeasurableSpace α}
  {μ : Measure α} [IsFiniteMeasure μ] {s : Finset ι} {f : ι → α → ℝ}
  (hf : ∀ i ∈ s, Integrable (f i) μ) :
  Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  induction' s using Finset.induction_on with a s ha ih
  case empty => simp
  case insert =>
    simp only [Finset.sum_insert ha]
    apply Integrable.add
    exact hf a (Finset.mem_insert_self a s)
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MeasureTheory
