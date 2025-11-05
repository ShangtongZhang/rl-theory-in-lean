/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang shangtong.zhang.cs@gmail.com
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

open MeasureTheory MeasureTheory.Measure  ProbabilityTheory Finset NNReal ENNReal Preorder Filter

namespace MeasureTheory.Measure

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma ae_join_of_ae_ae
  {m : Measure (Measure α)}
  {p : α → Prop} (hp : MeasurableSet {a | p a})
  (h : ∀ᵐ μ ∂ m, ∀ᵐ a ∂ μ, p a) :
  ∀ᵐ a ∂ m.join, p a := by
  apply ae_iff.mpr
  rw [join_apply]
  have := lintegral_zero (μ := m)
  apply Eq.symm
  apply this.symm.trans
  apply lintegral_congr_ae
  apply Eventually.mono h
  intro μ hμ
  simp
  apply Eq.symm
  apply ae_iff.mp
  exact hμ
  apply MeasurableSet.compl hp

lemma ae_bind_of_ae_ae
  {m : Measure α}
  {p : β → Prop} {hp : MeasurableSet {a | p a}}
  {f : α → Measure β}
  (hf : AEMeasurable f m)
  (h  : ∀ᵐ a ∂ m, ∀ᵐ b ∂ f a, p b) :
  ∀ᵐ b ∂ m.bind f, p b := by
  unfold Measure.bind
  apply ae_join_of_ae_ae hp
  set p' := fun ν : Measure β => ∀ᵐ b ∂ ν, p b
  apply (ae_map_iff ?_ ?_).mpr
  exact h
  exact hf
  let g := fun x : Measure β => x {a | ¬ p a}
  apply MeasurableSet.congr
  case h =>
    ext x
    apply Iff.intro
    case h.mpr =>
      intro h
      simp at h
      rw [ae_iff] at h
      have : x ∈ {x | g x = 0} := by unfold g; simp [h]
      have : x ∈ g ⁻¹' {0} := by unfold g; simp [h]
      exact this
    case h.mp =>
      intro h
      simp at h
      simp [g] at h
      rw [←ae_iff] at h
      simp [h]
  apply MeasurableSet.preimage
  simp
  simp [g]
  exact Measure.measurable_measure.mp measurable_id _ hp.compl


end MeasureTheory.Measure
