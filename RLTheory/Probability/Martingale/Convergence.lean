/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import RLTheory.Tactic.NatLeInd
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open TopologicalSpace Filter MeasureTheory.Filtration Finset NNReal
open scoped MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m₀}
variable {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem ae_summable_of_summable_integral
  {f : ℕ → Ω → ℝ}
  (hf : ∀ i, Integrable (f i) μ)
  (hfm : ∀ i, Measurable (f i))
  (hfnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
  (hfsum : Summable (fun n => ∫ ω, f n ω ∂μ)) :
  ∀ᵐ ω ∂μ, Summable (fun n => f n ω) := by
  let g := fun n ω => ENNReal.ofReal (f n ω)
  have hg : ∀ n, AEMeasurable (g n) μ := by
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hf n).aemeasurable
  have : ∀ᵐ ω ∂μ, ∑' n, g n ω < ⊤ := by
    let g' : ℕ → ℝ≥0 := fun n => (∫ ω, f n ω ∂μ).toNNReal
    apply ae_lt_top
    case h2f =>
      rw [lintegral_tsum]
      have : Summable g' := by
        unfold g'
        have := hfsum.toNNReal
        apply Summable.congr this
        intro n
        rw [Real.toNNReal_of_nonneg]
        exact integral_nonneg_of_ae (hfnonneg n)
      have := ENNReal.tsum_coe_ne_top_iff_summable.mpr this
      unfold g' at this
      unfold g
      by_contra h
      apply this _
      apply Eq.symm
      apply h.symm.trans
      apply tsum_congr
      intro n
      rw [integral_eq_lintegral_of_nonneg_ae]
      set x := ∫⁻ (a : Ω), ENNReal.ofReal (f n a) ∂μ
      rw [ENNReal.ofNNReal_toNNReal]
      rw [ENNReal.ofReal_toReal]
      unfold x
      apply ne_top_of_lt
      exact (hf n).lintegral_lt_top
      exact hfnonneg n
      exact (hf n).aestronglyMeasurable
      exact hg
    case hf =>
      apply Measurable.ennreal_tsum
      intro n
      exact ENNReal.measurable_ofReal.comp (hfm n)

  apply Eventually.mono (this.and (ae_all_iff.mpr hfnonneg))
  intro ω hω
  simp [g] at hω
  unfold Summable
  refine ⟨(∑' n, ENNReal.ofReal (f n ω)).toReal, ?_⟩
  apply (hasSum_iff_tendsto_nat_of_nonneg ?_ _).mpr
  have := ENNReal.tendsto_nat_tsum fun n => ENNReal.ofReal (f n ω)
  have := (ENNReal.tendsto_toReal hω.1.ne_top).comp this
  apply (Tendsto.congr ?_) this
  intro n
  simp
  rw [ENNReal.toReal_sum]
  apply sum_congr rfl
  simp
  simp [hω.2]
  simp
  exact hω.2


lemma Submartingale.uniform_bdd_l1_of_uniform_bdd_above
  (hf : Submartingale f ℱ μ)
  (hbdd : ∃ R : ℝ, ∀ n, μ[(f n)⁺] ≤ R)
  : ∃ R : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ R := by
  obtain ⟨hAdapted, hNondec, hInt⟩ := hf
  obtain ⟨R, hbdd⟩ := hbdd
  have hμfn : ∀ n, μ[(f n)⁻] = μ[(f n)⁺] - μ[f n] := by
    intro n
    simp
    rw [←integral_sub (hg := hInt n)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ω; simp
    linarith [posPart_sub_negPart (f n ω)]
    have := Integrable.pos_part (hInt n)
    exact this
  have hle : ∀ n, μ[f 0] ≤ μ[f n] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have := hNondec n (n + 1)
      simp at this
      have := integral_mono_ae (hInt n) integrable_condExp this
      have := ih.trans this
      rw [integral_condExp _ ] at this
      exact this
  have : ∀ n, μ[(f n)⁻] ≤ R - μ[f 0] := by
    intro n
    linarith [hμfn n, hle n, hbdd n]
  have : ∀ n, μ[fun ω => |f n ω|] ≤ 2 * R - μ[f 0] := by
    intro n
    rw [integral_congr_ae _]
    rotate_right
    apply Eventually.of_forall
    intro ω; simp
    rw [←posPart_add_negPart]
    rw [integral_add]
    case hf => have := Integrable.pos_part (hInt n); exact this
    case hg => have := Integrable.neg_part (hInt n); exact this
    have := hbdd n
    simp at this
    have := hμfn n
    simp at this
    have := hle n
    linarith
  let R' := |2 * R - μ[f 0]|
  have : ∀ n, μ[fun ω => |f n ω|] ≤ R' := by
    intro n
    have := this n
    unfold R'
    linarith [le_abs_self (2 * R - μ[f 0])]
  refine ⟨?R, ?hR⟩
  case R => exact ⟨R', by simp [R']⟩
  case hR =>
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm]
    have h := this n
    rw [integral_congr_ae ?_] at h
    rotate_right
    apply Eventually.of_forall
    intro x; simp
    rw [←Real.norm_eq_abs]
    have hf : AEStronglyMeasurable (f n) μ :=
      (hInt n).aemeasurable.aestronglyMeasurable
    have hfinite := integral_norm_eq_lintegral_enorm hf
    rw [hfinite] at h
    have h := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_toReal_eq_iff.mpr] at h
    have : 0 ≤ R' := by unfold R'; simp
    have := ENNReal.ofReal_eq_coe_nnreal this
    rw [this] at h
    exact h
    have := Integrable.lintegral_lt_top (hInt n).norm
    rw [lintegral_congr_ae ?_] at this
    rotate_right
    apply Eventually.of_forall
    intro x
    simp [-Real.norm_eq_abs]
    rfl
    exact this.ne

lemma sum_cancel_consecutive {α : Type*} [AddCommGroup α] {f : ℕ → α} {m n : ℕ} (hmn : m ≤ n) :
  ∑ i ∈ Ico m n, (f (i + 1) - f i) = f n - f m := by
  nat_le_ind n hmn
  case base => simp
  case succ =>
    intro n hmn hP
    rw [←Finset.Ico_union_Ico_eq_Ico (b := n), sum_union, hP]
    simp
    apply Ico_disjoint_Ico_consecutive
    exact hmn
    simp

theorem ae_tendsto_zero_of_almost_supermartingale
    (hAdapt : Adapted ℱ f)
    (hfm : ∀ n, Measurable (f n))
    (hfInt   : ∀ n, Integrable (f n) μ)
    (hfnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    {T : ℕ → ℝ}
    (hTpos   : ∀ n, 0 < T n)
    {hTsum : Tendsto (fun n => ∑ k ∈ range n, T k) atTop atTop}
    {hTsqsum : Summable (fun n => (T n) ^ 2)}
    (hAlmostSupermartingale :
      ∃ C ≥ 0, ∀ n, μ[f (n + 1) | ℱ n] ≤ᵐ[μ] (fun ω => (1 - T n) * f n ω + C * T n ^ 2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    obtain ⟨C, hC, hAlmostSupermartingale⟩ := hAlmostSupermartingale

    let tail := fun n => ∑' k, (T (k + n)) ^ 2
    let g := fun n (_ : Ω) => C * tail n
    have hgInt : ∀ n, Integrable (g n) μ := by
      intro n
      apply integrable_const
    let W := -f - g

    have hWInt : ∀ n, Integrable (W n) μ := by
      intro n
      simp [W, g]
      apply Integrable.sub
      exact (hfInt n).neg
      apply integrable_const

    have hWm : ∀ n, @StronglyMeasurable _ _ _ (ℱ n) (W n) := by
      intro n
      simp [W, g]
      apply StronglyMeasurable.sub
      apply StronglyMeasurable.neg
      exact (hAdapt n).stronglyMeasurable
      apply stronglyMeasurable_const

    have hW : ∀ n, W n + T n • f n ≤ᶠ[ae μ] μ[W (n + 1)|ℱ n] := by
      intro n
      simp [W]
      apply EventuallyLE.trans_eq
      case H₂ =>
        apply EventuallyEq.symm
        apply condExp_sub
        exact (hfInt (n + 1)).neg
        exact hgInt (n + 1)
      apply EventuallyLE.trans_eq
      case H₂ =>
        apply EventuallyEq.sub
        apply EventuallyEq.symm
        apply condExp_neg
        apply EventuallyEq.symm
        unfold g
        apply Eventually.of_forall
        intro ω
        have := condExp_const (μ := μ) (ℱ.le' n) (C * tail (n + 1))
        apply congrFun this
      apply Eventually.mono ((hAlmostSupermartingale n).and (hfnonneg n))
      intro ω hω
      simp at hω ⊢
      grw [hω.1]
      rw [neg_add, sub_mul, neg_sub]
      simp
      unfold g
      ring_nf
      rw [add_assoc]
      apply add_le_add
      simp
      rw [sub_eq_add_neg]
      apply add_le_add
      rfl
      apply le_of_neg_le_neg
      simp
      rw [←mul_add]
      gcongr
      unfold tail
      apply le_of_eq
      have := Summable.sum_add_tsum_nat_add n hTsqsum
      have := eq_sub_of_add_eq' this
      rw [this]
      have := Summable.sum_add_tsum_nat_add (1 + n) hTsqsum
      have := eq_sub_of_add_eq' this
      rw [this]
      ring_nf
      have : 1 + n = n + 1 := by linarith
      rw [this, sum_range_succ]
      ring

    have hWsub : Submartingale W ℱ μ := by
      refine ⟨?hAdapted, ?hle, hWInt⟩
      case hAdapted =>
        intro n
        simp [W]
        unfold g
        apply StronglyMeasurable.sub
        apply StronglyMeasurable.neg
        exact (hAdapt n).stronglyMeasurable
        apply stronglyMeasurable_const
      case hle =>
        intro i
        refine Nat.le_induction ?base ?step
        case base =>
          have := condExp_of_aestronglyMeasurable' _ (hWm i).aestronglyMeasurable (hWInt i)
          exact this.symm.le
        case step =>
          intro n hn hin
          have : W n ≤ᶠ[ae μ] μ[W (n + 1)|ℱ n] := by
            apply Eventually.mono ((hW n).and (hfnonneg n))
            intro ω hω
            simp at hω
            apply le_of_add_le_of_nonneg_left hω.1
            apply mul_nonneg (hTpos n).le hω.2
          have := condExp_mono (m := ℱ i) (hWInt n) ?_ this
          have hin := hin.trans this
          exact hin.trans_eq (condExp_condExp (μ := μ) (W (n + 1)) ℱ hn)
          apply integrable_condExp

    have : ∀ n, μ[(W n)⁺] ≤ 0 := by
      intro n
      have : (W n)⁺ ≤ᵐ[μ] 0 := by
        apply Eventually.mono (hfnonneg n)
        intro ω hω
        simp [W, g]
        apply posPart_nonpos.mpr
        simp at hω
        rw [neg_sub_left]
        apply neg_nonpos.mpr
        apply add_nonneg _ hω
        apply mul_nonneg hC.le
        unfold tail
        apply tsum_nonneg
        intro n
        apply sq_nonneg
      have := integral_mono_ae ?_ ?_ this
      grw [this]
      simp
      apply Integrable.pos_part (hWInt n)
      apply integrable_const

    have := hWsub.uniform_bdd_l1_of_uniform_bdd_above ⟨0, this⟩
    obtain ⟨R, hR⟩ := this
    have hWtendsto := hWsub.exists_ae_tendsto_of_bdd hR
    have hftendsto : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
      apply Eventually.mono hWtendsto
      intro ω hω
      obtain ⟨c, hc⟩ := hω
      simp [W, g] at hc
      refine ⟨-c, ?_⟩
      have : Tendsto tail atTop (𝓝 0) := by
        unfold tail
        apply Tendsto.congr
        intro n
        have := Summable.sum_add_tsum_nat_add n hTsqsum
        have := eq_sub_of_add_eq' this
        exact this.symm
        have := hTsqsum.tendsto_sum_tsum_nat
        have := this.const_sub (b := ∑' (i : ℕ), T i ^ 2)
        simp at this
        exact this
      have := (hc.add (this.const_mul C)).neg
      unfold tail at this
      simp at this
      exact this

    have : Summable (fun n => μ[T n • f n]) := by
      set g := fun n => μ[T n • f n]
      have hg : ∀ n, 0 ≤ g n := by
        intro n
        apply integral_nonneg_of_ae
        apply Eventually.mono (hfnonneg n)
        intro ω hω
        simp at hω ⊢
        apply mul_nonneg
        exact (hTpos n).le
        exact hω
      have hgub : ∀ n, μ[T n • f n] ≤ μ[W (n + 1)] - μ[W n] := by
        intro n
        have := integral_mono_ae ?_ ?_ (hW n)
        simp at this
        rw [integral_condExp _, integral_add] at this
        simp
        linarith
        exact hWInt n
        exact (hfInt n).const_mul (T n)
        exact (hWInt n).add ((hfInt n).const_mul (T n))
        apply integrable_condExp
      have : ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, g i) atTop (𝓝 l) := by
        have hmono : Monotone fun n => ∑ i ∈ range n, g i := by
          intro m n hmn
          apply sum_mono_set_of_nonneg
          exact hg
          simp
          exact hmn
        apply Or.resolve_left
        apply tendsto_of_monotone hmono
        by_contra hcontra
        have := (tendsto_atTop_atTop_iff_of_monotone hmono).mp hcontra
        apply absurd this
        push_neg
        refine ⟨R + |μ[W 0]| + 1, ?hub⟩
        case hub =>
          intro n
          simp [g]
          apply lt_of_le_of_lt
          apply sum_le_sum
          intro i hi
          exact hgub i
          have : range n = Ico 0 n := by simp
          rw [this]
          rw [sum_cancel_consecutive (f := fun n => ∫ ω, W n ω ∂μ) (by simp)]
          have := hR n
          simp [eLpNorm_one_eq_lintegral_enorm] at this
          apply lt_of_le_of_lt
          case hbc.b => exact R + |μ[W 0]|
          apply le_of_abs_le
          rw [sub_eq_add_neg]
          grw [abs_add_le]
          rw [abs_neg]
          simp
          rw [←Real.norm_eq_abs]
          grw [norm_integral_le_lintegral_norm]
          apply ENNReal.toReal_le_coe_of_le_coe
          simp
          grw [lintegral_ofReal_le_lintegral_enorm]
          simp [this]
          simp
      refine ⟨this.choose, ?hc⟩
      case hc =>
        apply (hasSum_iff_tendsto_nat_of_nonneg ?_ _).mpr
        exact this.choose_spec
        exact hg

    have := ae_summable_of_summable_integral ?_ ?_ ?_ this
    apply Eventually.mono ((this.and hftendsto).and (ae_all_iff.mpr hfnonneg))
    intro ω hω
    simp at hω
    obtain ⟨c, hc⟩ := hω.1.2
    have : 0 = c := by
      by_contra h
      have : 0 ≤ c := by
        apply le_of_tendsto_of_tendsto' (f := 0) _ hc
        intro n
        simp
        exact hω.2 n
        apply tendsto_const_nhds
      have hcpos : 0 < c := by apply lt_of_le_of_ne this h
      set ε := c / 2 with hε
      have := Metric.tendsto_atTop.mp hc ε (by simp [ε, hcpos])
      obtain ⟨n₀, hn₀⟩ := this
      have hflb : ∀ n ≥ n₀, ε < f n ω := by
        intro n hn
        have h := hn₀ n hn
        simp [dist] at h
        unfold ε at h ⊢
        have := le_abs_self (c - f n ω)
        rw [←abs_neg, neg_sub] at this
        linarith
      apply absurd hω.1.1
      apply (not_summable_iff_tendsto_nat_atTop_of_nonneg ?_).mpr
      apply (tendsto_add_atTop_iff_nat n₀).mp

      have := hTsum.atTop_mul_const (r := ε) (by linarith)
      have := (tendsto_add_atTop_iff_nat n₀).mpr this
      have := tendsto_atTop_add_const_right atTop
        (∑ k ∈ range n₀, T k * f k ω - ∑ k ∈ range n₀, T k * ε) this
      apply tendsto_atTop_mono' atTop ?_ this
      apply Filter.eventually_atTop.mpr
      refine ⟨n₀, ?hN⟩
      case hN =>
        intro n hn
        simp
        rw [sum_mul]
        simp_rw [range_eq_Ico]
        have := Ico_union_Ico_eq_Ico
          (a := 0) (b := n₀) (c := n + n₀) (by simp) (by simp)
        simp_rw [←this]
        rw [sum_union, sum_union]
        nth_rw 2 [add_comm]
        rw [add_add_sub_cancel]
        rw [add_comm]
        apply add_le_add
        rfl
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left
        apply le_of_lt
        apply hflb i
        simp [mem_Ico.mp hi]
        apply le_of_lt
        apply hTpos
        apply Ico_disjoint_Ico_consecutive
        apply Ico_disjoint_Ico_consecutive
      intro n
      apply mul_nonneg
      apply le_of_lt
      apply hTpos
      apply hω.2
    simp [←this] at hc
    exact hc

    intro n
    apply Integrable.smul
    exact hfInt n
    intro n
    apply Measurable.const_mul
    exact hfm n
    intro n
    apply Eventually.mono (hfnonneg n)
    intro ω hω
    simp at hω ⊢
    apply mul_nonneg
    exact (hTpos n).le
    exact hω

end MeasureTheory
