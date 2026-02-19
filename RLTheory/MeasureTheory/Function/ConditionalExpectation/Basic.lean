/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
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
  (hfgInt : ∀ i, Integrable ((fun ω ↦ (f ω).ofLp i) * fun ω ↦ (g ω).ofLp i) μ)
  (hf : ∀ i, AEStronglyMeasurable[m] (fun ω ↦ (f ω).ofLp i) μ) :
  μ[fun ω => ⟪f ω, g ω⟫ | m] =ᵐ[μ] fun ω => ⟪f ω, μ[g|m] ω⟫ := by
    -- Convert inner product to sum form
    have inner_eq : ∀ x y : EuclideanSpace ℝ (Fin d), ⟪x, y⟫ = ∑ i, x.ofLp i * y.ofLp i := by
      intro x y
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      rw [dotProduct_comm]
      rfl
    simp_rw [inner_eq]
    have hgiInt : ∀ i, Integrable (fun ω => (g ω).ofLp i) μ := by
      intro i
      exact ContinuousLinearMap.integrable_comp
        (𝕜 := ℝ) (EuclideanSpace.proj i) hgInt
    have heq : (fun ω => ∑ i, (f ω).ofLp i * (g ω).ofLp i)
      = ∑ i, (fun ω => (f ω).ofLp i) * (fun ω => (g ω).ofLp i) := by
        ext ω
        simp [Finset.sum_apply]
    rw [heq]
    apply EventuallyEq.trans
    apply condExp_finset_sum
    intro i hi
    exact hfgInt i
    -- Show that for each i, the component of condExp equals condExp of component
    have hproj : ∀ i, μ[fun ω => (g ω).ofLp i | m] =ᵐ[μ] fun ω => (μ[g|m] ω).ofLp i := by
      intro i
      have hcomp := ContinuousLinearMap.condExp_comp
        (f := g) (L := EuclideanSpace.proj i) (μ := μ) (hm := hm) hgInt
      exact hcomp
    apply EventuallyEq.trans
    apply EventuallyEq.finset_sum
    intro i hi
    apply EventuallyEq.trans
    apply condExp_mul_of_aestronglyMeasurable_left
    exact hf i
    exact hfgInt i
    exact hgiInt i
    apply EventuallyEq.mul
    apply EventuallyEq.refl
    exact hproj i
    apply Eventually.of_forall
    intro ω
    simp only [Finset.sum_apply, Pi.mul_apply]

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
