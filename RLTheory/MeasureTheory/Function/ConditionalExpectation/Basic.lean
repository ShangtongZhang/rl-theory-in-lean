/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Analysis.Convex.Integral

import RLTheory.Defs
import RLTheory.Order.Filter.Basic
import RLTheory.MeasureTheory.Function.L1Space.Integrable

open Filter ProbabilityTheory
open scoped RealInnerProductSpace

namespace MeasureTheory

theorem ContinuousLinearMap.condExp_comp
  {Ω α β: Type*}
  [MeasurableSpace α]
  [NormedAddCommGroup α]
  [NormedSpace ℝ α]
  [CompleteSpace α]
  [BorelSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
  [MeasurableSpace β]
  [SecondCountableTopology β]
  [BorelSpace β]
  {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} (hm : m ≤ m₀)
  [SigmaFinite (μ.trim hm)]
  {f : Ω → α} (hf : Integrable f μ) (L : α →L[ℝ] β)
  : μ[L ∘ f| m] =ᵐ[μ] L ∘ (μ[f | m]) := by
  apply EventuallyEq.trans
  apply EventuallyEq.symm (f := L ∘ (μ[f | m]))
  apply ae_eq_condExp_of_forall_setIntegral_eq
  case hg_eq =>
    intro s hs hμs
    simp
    rw [L.integral_comp_comm]
    rw [L.integral_comp_comm]
    apply congr_arg
    rw [setIntegral_condExp]
    exact hf
    exact hs
    apply Integrable.restrict
    exact hf
    apply Integrable.restrict
    apply integrable_condExp
  apply ContinuousLinearMap.integrable_comp
  exact hf
  intro s hs hμs
  apply Integrable.restrict
  apply ContinuousLinearMap.integrable_comp
  apply integrable_condExp
  apply Measurable.aestronglyMeasurable
  apply Measurable.comp
  apply L.continuous.measurable
  apply StronglyMeasurable.measurable
  apply stronglyMeasurable_condExp
  apply Eventually.of_forall
  simp

theorem condExp_inner
  {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω} {d : ℕ}
  {f g : Ω → EuclideanSpace ℝ (Fin d)}
  (hm : m ≤ m₀)
  [SigmaFinite (μ.trim hm)]
  (hgInt : Integrable g μ)
  (hfgInt : ∀ i, Integrable ((fun ω ↦ f ω i) * fun ω ↦ g ω i) μ)
  (hf : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ f ω i) μ) :
  μ[fun ω => ⟪f ω, g ω⟫ | m] =ᵐ[μ] fun ω => ⟪f ω, μ[g|m] ω⟫ := by
    simp
    have hgiInt : ∀ i, Integrable (fun ω => g ω i) μ := by
      intro i
      exact ContinuousLinearMap.integrable_comp
        (𝕜 := ℝ) (EuclideanSpace.proj i) hgInt
    have : (fun ω => ∑ i, g ω i * f ω i)
      = ∑ i, (fun ω => f ω i) * (fun ω => g ω i) := by
        ext ω
        simp [Finset.sum_apply, mul_comm]
    rw [this]
    apply EventuallyEq.trans
    apply condExp_finset_sum
    intro i hi
    exact hfgInt i
    apply EventuallyEq.trans
    apply EventuallyEq.finset_sum
    intro i hi
    apply EventuallyEq.trans
    apply condExp_mul_of_aestronglyMeasurable_left
    exact hf i
    exact hfgInt i
    exact hgiInt i
    have := ContinuousLinearMap.condExp_comp
      (f := g) (L := EuclideanSpace.proj i) (μ := μ) (hm := hm) ?_
    apply Eventually.mono this
    intro ω hω
    simp
    case g => exact fun i ω => f ω i * μ[g|m] ω i
    simp
    apply Or.inl
    refine Eq.trans ?_ (Eq.trans hω ?_)
    apply congrFun
    apply congrArg
    ext ω
    simp
    simp
    exact hgInt
    apply Eventually.of_forall
    intro ω
    simp
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_comm]

theorem norm_condExp_le_condExp_norm
  {Ω : Type*} {m m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {μ : Measure[m₀] Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ} {f : Ω → EuclideanSpace ℝ (Fin d)}
  (hf_i : Integrable f μ)
  (hf_m : Measurable f)
  (hf_bdd : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
  (hm : m ≤ m₀) :
  (fun ω => ‖μ[f | m] ω‖) ≤ᵐ[μ] fun ω => μ[fun ω => ‖f ω‖ | m] ω := by
  have hf : ∀ ω, Integrable f ((condExpKernel μ m) ω) := by
    intro ω
    apply integrable_of_norm_le
    apply hf_m.aestronglyMeasurable
    use hf_bdd.choose
    apply Eventually.of_forall
    exact hf_bdd.choose_spec
  apply EventuallyLE.trans
  apply Eventually.mono (condExp_ae_eq_integral_condExpKernel hm hf_i)
  intro ω hω
  simp at hω ⊢
  rw [hω]
  apply EventuallyLE.trans ?_
  apply Eventually.mono (condExp_ae_eq_integral_condExpKernel hm hf_i.norm)
  intro ω hω
  simp at hω ⊢
  rw [hω]
  apply Eventually.mono ?_
  intro ω
  apply ConvexOn.map_integral_le (s := Set.univ)
  apply convexOn_univ_norm
  apply ContinuousOn.norm
  apply continuousOn_id
  simp
  simp
  apply hf
  apply Eventually.of_forall
  intro ω
  apply (hf ω).norm

end MeasureTheory
