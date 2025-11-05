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

lemma prod_preimage_snd
  (μ : Measure α) (ν : Measure β) (hν : SFinite ν) (A : Set β) :
  (μ.prod ν) (Prod.snd ⁻¹' A) = μ Set.univ * ν A := by
    have : Prod.snd ⁻¹' A = (Set.univ : Set α) ×ˢ A := by
      ext p; rcases p with ⟨x,y⟩; simp
    have := congrArg (fun x => (μ.prod ν) x) this
    simp at this
    exact this

lemma prod_preimage_fst
  (μ : Measure α) (ν : Measure β) (hν : SFinite ν) (A : Set α) :
  (μ.prod ν) (Prod.fst ⁻¹' A) = μ A * ν Set.univ := by
    have : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set β) := by
      ext p; rcases p with ⟨x,y⟩; simp
    have := congrArg (fun x => (μ.prod ν) x) this
    simp at this
    exact this

lemma map_prodMk_dirac
  {X : α → β} {Y : α → γ} {μ : Measure α}
  {C : β} (hC : ∀ᵐ a ∂μ, X a = C)
  (hY : Measurable Y) [SFinite (Measure.map Y μ)]:
  (Measure.map (fun a ↦ (X a, Y a)) μ) =
    (Measure.dirac C).prod (Measure.map Y μ) := by
  apply Eq.trans
  apply Measure.map_congr
  apply Eventually.mono hC
  simp
  intro x hx
  rw [hx]
  rw [dirac_prod]
  rw [Measure.map_map]
  apply congrArg μ.map
  ext x
  simp
  simp
  measurability
  exact hY

end MeasureTheory.Measure
