/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

import RLTheory.Defs
import RLTheory.StochasticApproximation.Pathwise
import RLTheory.StochasticApproximation.StepSize
import RLTheory.Probability.Martingale.Convergence
import RLTheory.MeasureTheory.Function.ConditionalExpectation.Basic
import RLTheory.MeasureTheory.Function.L1Space.Integrable
import RLTheory.Order.Filter.Basic

open NNReal Real Finset Filter TopologicalSpace Filter MeasureTheory.Filtration ENNReal MeasureTheory RLTheory
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology InnerProductSpace RealInnerProductSpace Gradient

namespace MeasureTheory
variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

namespace Filtration

def shift (ℱ : Filtration ℕ m₀) (n : ℕ) : Filtration ℕ m₀ := by
  constructor
  case seq => exact fun t => ℱ (t + n)
  case le' =>
    intro i
    exact ℱ.le (i + n)
  case mono' =>
    intro i j hij
    exact ℱ.mono (Nat.add_le_add_right hij n)

end Filtration


end MeasureTheory


namespace StochasticApproximation

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m₀}

variable {d : ℕ}
variable {x₀ : E d}
variable {α : ℕ → ℝ}
variable {f : E d → E d}
variable {e₁ e₂ :  ℕ → Ω → E d}

lemma le_of_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : √a ≤ √b)
  : a ≤ b := by
  have := abs_le_abs_of_nonneg (by simp) h
  have := sq_le_sq.mpr this
  rw [Real.sq_sqrt] at this
  rw [Real.sq_sqrt] at this
  exact this
  exact hb
  exact ha

theorem ae_tendsto_of_iterates_mds_noise
  {x : ℕ → Ω → E d}
  (hx : Iterates x x₀ f e₁ e₂ α)
  (he₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n,
    ‖e₁ (n + 1) ω‖ ≤ C * (α n) * (‖x n ω‖ + 1))
  (he₁Adapted : Adapted (ℱ.shift 1) (fun n => e₁ (n + 1)))
  (he₁MDS : ∀ n, μ[e₁ (n + 1)|ℱ n] =ᵐ[μ] 0)
  (he₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n,
    ‖e₂ (n + 1) ω‖ ≤ C * (α n) ^ 2 * (‖x n ω‖ + 1))
  (he₂Adapted : Adapted (ℱ.shift 1) (fun n => e₂ (n + 1)))
  (hα : RobbinsMonro (α := α))
  {z : E d}
  (hz : z = f z)
  (hfm : Measurable f)
  (hfLip : ∃ L, LipschitzWith L f)
  {φ : E d → ℝ}
  {φ' : E d → E d}
  (hφm : Measurable φ)
  (hgradφm : Measurable φ')
  [LyapunovFunction φ φ' f] :
  ∀ᵐ ω ∂μ, Tendsto (fun n => x n ω) atTop (𝓝 z) := by
  have hEnergy : LyapunovFunction φ φ' f := by infer_instance
  have hxbdd := bdd_of_iterates hx he₁ he₂ hfLip hα.pos
  have := fundamental_inequality hx he₁ he₂ hz hfLip hα.pos hα.sqsum
    (φ := φ) (φ' := φ')
  obtain ⟨B₁, B₂, hB₁pos, hB₂nonneg, n₀, hAlmostSupermartingale⟩ := this
  obtain ⟨C₀, hC₀nonneg, hC₀⟩ := hEnergy.norm_le
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := hEnergy.le_norm
  obtain ⟨C₂, hC₂nonneg, hC₂⟩ := hEnergy.inner_grad_le'
  obtain ⟨C₃, hC₃nonneg, hC₃⟩ := he₁

  have : ∀ᵐ ω ∂μ, Tendsto (fun n => φ (x n ω - z)) atTop (𝓝 0) := by
    have : ∀ᵐ (ω : Ω) ∂μ,
      Tendsto (fun n ↦ φ (x (n + n₀) ω - z)) atTop (𝓝 0) := by
      let ℱ' := ℱ.shift n₀
      have hxm : ∀ n, Measurable[ℱ n] (x n) := by
        intro n
        induction' n with n ih
        case zero =>
          have : x 0 = fun ω => x₀ := by
            ext1 ω
            apply hx.init
          rw [this]
          apply measurable_const
        case succ =>
          have := hx.step n
          rw [←funext_iff] at this
          rw [this]
          have : Measurable[ℱ (n + 1)] (x n) := by
            apply ih.mono
            apply ℱ.mono
            simp
            rfl
          apply Measurable.add
          apply Measurable.add
          apply Measurable.add
          exact this
          apply Measurable.smul
          simp
          apply Measurable.sub
          apply hfm.comp
          exact this
          exact this
          apply (he₁Adapted n).measurable.mono
          apply ℱ.mono
          simp
          rfl
          apply (he₂Adapted n).measurable.mono
          apply ℱ.mono
          simp
          rfl

      have hφnm : ∀ (n : ℕ), Measurable
        (fun ω ↦ φ (x (n + n₀) ω - z)) := by
        intro n
        apply Measurable.comp
        exact hφm
        apply Measurable.sub_const
        apply (hxm (n + n₀)).mono
        apply ℱ.le
        simp
      have hφnInt : ∀ (n : ℕ), Integrable
        (fun ω ↦ φ (x (n + n₀) ω - z)) μ := by
        intro n
        apply integrable_of_norm_le (hφnm n).aestronglyMeasurable
        obtain ⟨C₃, hC₃pos, hC₃⟩ := hxbdd (n + n₀)
        let C := (C₁ * (C₃ + ‖z‖)) ^ 2
        refine ⟨C, ?hC⟩
        case hC =>
          apply Eventually.mono hC₃
          intro ω hC₃
          simp [norm_eq_abs]
          rw [abs_of_nonneg]
          apply le_of_sqrt_le
          apply hEnergy.nonneg
          positivity
          grw [hC₁, norm_sub_le, hC₃]
          rw [Real.sqrt_sq]
          positivity
          apply hEnergy.nonneg
      apply ae_tendsto_zero_of_almost_supermartingale
      case ℱ => exact ℱ'
      case T => exact fun n => B₁ * α (n + n₀)
      case hfInt => exact hφnInt
      case hfm => exact hφnm
      case hfnonneg =>
        intro n
        apply Eventually.of_forall
        intro ω
        simp
        apply hEnergy.nonneg
      case hTpos =>
        intro n
        have := hα.pos (n + n₀)
        positivity
      case hTsum =>
        have := (tendsto_add_atTop_iff_nat n₀).mpr hα.sum
        have := this.const_mul_atTop hB₁pos
        have := tendsto_atTop_add_const_right
          atTop (-∑ i ∈ range n₀, B₁ * α i) this
        apply (tendsto_congr _).mp this
        intro n
        rw [mul_sum, ←sub_eq_add_neg]
        rw [range_eq_Ico]
        rw [←Ico_union_Ico_eq_Ico (a := 0) (b := n₀) (c := n + n₀)]
        rw [sum_union]
        simp
        rw [sum_Ico_eq_sum_range]
        simp [add_comm]
        apply Ico_disjoint_Ico_consecutive
        simp
        simp
      case hTsqsum =>
        obtain ⟨lim, hlim⟩ := hα.sqsum.mul_left (B₁ ^ 2)
        have := (hasSum_nat_add_iff' n₀).mpr hlim
        apply Summable.congr this.summable
        intro n
        simp [mul_pow]
      case hAdapt =>
        intro n
        simp
        apply Measurable.stronglyMeasurable
        apply Measurable.comp
        exact hφm
        apply Measurable.sub_const
        apply hxm

      case hAlmostSupermartingale =>
        refine ⟨B₂ / B₁ ^ 2, ?hCnonneg, ?hC⟩
        case hCnonneg =>
          apply div_nonneg
          exact hB₂nonneg
          apply sq_nonneg
        case hC =>
          intro n

          obtain ⟨Cx, hCxpos, hCx⟩ := hxbdd (n + n₀)
          set f₁ := fun ω => (1 - B₁ * α (n + n₀)) * φ (x (n + n₀) ω - z)
          have hf₁ : Integrable f₁ μ := by
            apply Integrable.const_mul
            exact hφnInt n
          set f₂ := fun ω =>
            ⟪φ' (x (n + n₀) ω - z), e₁ (n + n₀ + 1) ω⟫

          have hgradφim : ∀ i, AEStronglyMeasurable[ℱ (n + n₀)]
            (fun a ↦ φ' (x (n + n₀) a - z) i) μ := by
            intro i
            apply Measurable.aestronglyMeasurable
            apply Measurable.comp (g := fun x : E d => x i)
            apply measurable_pi_apply
            apply hgradφm.comp
            apply Measurable.sub_const
            apply hxm

          have hf₂im : ∀ i, AEStronglyMeasurable
            (fun a ↦ e₁ (n + n₀ + 1) a i * φ' (x (n + n₀) a - z) i) μ := by
            intro i
            apply AEStronglyMeasurable.mul
            apply Measurable.aestronglyMeasurable
            apply Measurable.comp (g := fun x : E d => x i)
            apply measurable_pi_apply
            have := he₁Adapted (n + n₀)
            simp [shift] at this
            exact (this.mono (ℱ.le (n + n₀ + 1))).measurable
            apply (hgradφim i).mono
            apply ℱ.le

          have hf₂m : AEStronglyMeasurable f₂ μ := by
            unfold f₂
            simp
            apply Finset.aestronglyMeasurable_sum
            intro i hi
            exact hf₂im i

          have hf₂i : ∀ i, Integrable
            (fun a ↦ e₁ (n + n₀ + 1) a i * φ' (x (n + n₀) a - z) i) μ := by
            intro i
            apply integrable_of_norm_le (hf₂im i)
            let C := C₂ * (C₁ * (Cx + ‖z‖)) *
              (C₁ * (C₃ * α (n + n₀) * (Cx + 1)))
            refine ⟨C, ?hC⟩
            case hC =>
              apply Eventually.mono (hC₃.and hCx)
              intro ω hω
              obtain ⟨hC₃, hCx⟩ := hω
              rw [norm_eq_abs, abs_mul, mul_comm]
              grw [single_le_sum (f := fun i =>
                |φ' (x (n + n₀) ω - z) i| * |e₁ (n + n₀ + 1) ω i|)]
              grw [hC₂, hC₁, hC₁, norm_sub_le, hC₃, hCx]
              have := hα.pos (n + n₀)
              positivity
              apply mul_nonneg hC₃nonneg
              exact (hα.pos (n + n₀)).le
              intro i hi
              positivity
              simp

          have hf₂ : Integrable f₂ μ := by
            simp [f₂]
            apply Integrable.finset_sum
            intro i hi
            exact hf₂i i

          set f₃ := fun ω ↦ B₂ * α (n + n₀) ^ 2
          have hf₃ : Integrable f₃ μ := by
            apply integrable_const

          apply EventuallyLE.trans
          apply condExp_mono (g := f₁ + f₂ + f₃)
          apply hφnInt
          exact (hf₁.add hf₂).add hf₃
          apply Eventually.mono hAlmostSupermartingale
          intro ω hω
          simp
          rw [add_assoc, add_comm 1 n₀, ←add_assoc]
          exact hω (n + n₀) (by simp)

          have : μ[f₁ + f₂ + f₃ | ℱ' n] =ᶠ[ae μ]
            μ[f₁ | ℱ' n] + μ[f₂ | ℱ' n] + μ[f₃ | ℱ' n] := by
            apply EventuallyEq.trans
            apply EventuallyEq.trans
            apply condExp_add
            exact hf₁.add hf₂
            exact hf₃
            apply EventuallyEq.add
            apply condExp_add
            exact hf₁
            exact hf₂
            rfl
            rfl
          apply EventuallyEq.trans_le this
          have hf₁ : μ[f₁ | ℱ' n] =ᶠ[ae μ] f₁ := by
            apply condExp_of_aestronglyMeasurable'
            apply Measurable.aestronglyMeasurable
            apply Measurable.const_mul
            apply Measurable.comp
            exact hφm
            apply Measurable.sub_const
            apply hxm
            exact hf₁
          have hf₂ : μ[f₂ | ℱ' n] =ᶠ[ae μ] 0 := by
            unfold f₂
            let g₁ := fun ω => e₁ (n + n₀) ω
            let g₂ := fun ω => ∇ φ (x (n + n₀) ω - z)
            apply EventuallyEq.trans
            apply condExp_inner
            case H₂ =>
              apply Eventually.mono (he₁MDS (n + n₀))
              intro ω hω
              simp [-PiLp.inner_apply]
              apply inner_eq_zero_of_right
              simp
              exact hω
            apply integrable_of_norm_le
            apply (he₁Adapted (n + n₀)).aestronglyMeasurable.mono
            apply ℱ.le
            refine ⟨C₃ * α (n + n₀) * (Cx + 1), ?hC⟩
            case hC =>
              apply Eventually.mono (hC₃.and hCx)
              intro ω hω
              obtain ⟨hC₃, hCx⟩ := hω
              grw [hC₃ (n + n₀)]
              grw [hCx]
              apply mul_nonneg hC₃nonneg
              apply (hα.pos (n + n₀)).le
            intro i
            apply Integrable.congr (hf₂i i)
            apply Eventually.of_forall
            simp [mul_comm]
            apply hgradφim
          have hf₃ : μ[f₃ | ℱ' n] =ᶠ[ae μ] f₃ := by
            apply condExp_of_aestronglyMeasurable'
            apply aestronglyMeasurable_const
            apply integrable_const
          have := (hf₁.add hf₂).add hf₃
          simp [←Pi.add_def] at this
          apply EventuallyEq.le
          apply this.trans
          apply EventuallyEq.add
          simp [f₁]
          simp [f₃]
          apply Eventually.of_forall
          intro ω
          simp
          rw [mul_pow, ←mul_assoc, div_mul_cancel₀]
          simp
          exact hB₁pos.ne'

    apply Eventually.mono this
    intro ω hTendsto
    exact (tendsto_add_atTop_iff_nat n₀).mp hTendsto
  apply Eventually.mono this
  intro ω hω
  have : Tendsto (fun n ↦ x n ω - z) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := 0)
    case hfh =>
      intro n
      simp
      apply hC₀
    apply tendsto_const_nhds
    have := hω.sqrt.mul_const C₀
    simp at this
    apply (tendsto_congr _).mp this
    intro n
    simp [mul_comm]
    intro n
    simp
  have := this.add_const z
  simp at this
  exact this

end StochasticApproximation
