/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.MoveAdd
import Mathlib.Order.Restriction
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Mathlib.Algebra.Order.Ring.Basic

import RLTheory.Defs
import RLTheory.Analysis.Normed.Group.Basic
import RLTheory.StochasticApproximation.Lyapunov
import RLTheory.StochasticApproximation.Iterates

open NNReal Real Finset Filter Preorder MeasureTheory RLTheory
open scoped Topology InnerProductSpace RealInnerProductSpace Gradient

namespace StochasticApproximation

variable {d : ℕ}
variable {x₀ : E d}

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

variable {α : ℕ → ℝ}
variable {hαpos : ∀ n, 0 < α n}
variable {hαsum : Tendsto (fun n => ∑ k ∈ range n, α k) atTop atTop}
variable {hαsqsum : Summable (fun n => (α n) ^ 2)}
variable {f : E d → E d}
variable {e₁ e₂ : ℕ → Ω → E d}

lemma LyapunovFunction.norm_add_le
  {φ : E d → ℝ}
  {φ' f : E d → E d}
  [LyapunovFunction φ φ' f] :
  ∀ z, z = f z → ∀ a, 0 ≤ a → ∃ C, 0 ≤ C ∧
    ∀ x, ‖x‖ + a ≤ C * (√(φ (x - z)) + 1) := by
  intro z hz a ha
  have hEnergy : LyapunovFunction φ φ' f := by infer_instance
  obtain ⟨C, hCpos, hC⟩ := hEnergy.norm_le (φ := φ)
  refine ⟨max C (a + ‖z‖), ?hCpos, ?hC⟩
  case hC =>
    intro x
    have : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by apply norm_le_insert'
    grw [this]
    grw [hC (x - z)]
    move_add [←a]
    apply LE.le.trans
    apply add_le_add
    have : a + ‖z‖ ≤ max C (a + ‖z‖) := by apply le_max_right
    exact this
    apply mul_le_mul_of_nonneg_right
    have : C ≤ max C (a + ‖z‖) := by apply le_max_left
    exact this
    apply Real.sqrt_nonneg
    linarith
  case hCpos =>
    apply hCpos.trans
    simp

set_option maxHeartbeats 300000 in
theorem fundamental_inequality
  {x : ℕ → Ω → E d}
  (hx : Iterates x x₀ f e₁ e₂ α)
  (he₁ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n, ‖e₁ (n + 1) ω‖ ≤ C * (α n) * (‖x n ω‖ + 1))
  (he₂ : ∃ C, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ n,
    ‖e₂ (n + 1) ω‖ ≤ C * (α n) ^ 2 * (‖x n ω‖ + 1))
  {z : E d}
  (hz : z = f z)
  (hfLip : ∃ L, LipschitzWith L f)
  (hαpos : ∀ n, 0 < α n)
  (hαsqsum : Summable (fun n => (α n) ^ 2))
  {φ : E d → ℝ}
  {φ' : E d → E d}
  [LyapunovFunction φ φ' f] :
  ∃ B₁ B₂, 0 < B₁ ∧ 0 ≤ B₂ ∧ ∃ n₀, ∀ᵐ ω ∂μ, ∀ n, n ≥ n₀ →
    φ (x (n + 1) ω - z) ≤ (1 - B₁ * α n) * φ (x n ω - z) +
      ⟪φ' (x n ω - z), e₁ (n + 1) ω⟫ + B₂ * (α n) ^ 2 := by
  obtain ⟨Lf, hfLip⟩ := hfLip
  have hfLip := lipschitzWith_iff_norm_sub_le.mp hfLip
  have hEnergy : LyapunovFunction φ φ' f := by infer_instance
  obtain ⟨L, hLnonneg, hL⟩ := hEnergy.smooth
  obtain ⟨η, hηpos, hdecrease⟩ := hEnergy.decrease
  have hdecrease := hdecrease z hz
  obtain ⟨C₀, hC₀nonneg, hC₀⟩ := hEnergy.norm_le
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := hEnergy.le_norm
  obtain ⟨C₃, hC₃nonneg, hC₃⟩ := he₁
  obtain ⟨C₄, hC₄nonneg, hC₄⟩ := he₂
  obtain ⟨C₅, hC₅nonneg, hC₅⟩ := hEnergy.norm_add_le z hz 1 (by linarith)
  obtain ⟨C₆, hC₆nonneg, hC₆⟩ := hEnergy.inner_grad_le

  let B₁ := η
  let B₂ := C₁ * C₆ * C₄ * C₅ +
    C₆ * C₁ * C₄ * C₅ + L * 2 * 2 * Lf ^ 2 * C₀ ^ 2 +
    L * 2 * 2 * C₀ ^ 2 + L * 2 * C₃ ^ 2 * C₅ ^ 2 * 2
  let B₃ := L * C₄ ^ 2 * C₅ ^ 2 * 2
  let B₄ := C₆ * C₁ * C₄ * C₅ + L * 2 * C₃ ^ 2 * C₅ ^ 2 * 2
  let B₅ := L * C₄ ^ 2 * C₅ ^ 2 * 2
  have : 0 ≤ B₂ := by positivity
  have : 0 ≤ B₃ := by positivity

  let ε := min 1 (B₁ / (2 * (B₂ + B₃ + 1)))
  have hεpos : 0 < ε := by
    apply lt_min
    linarith
    apply div_pos
    exact hηpos
    linarith

  obtain ⟨n₀, hn₀⟩ :=
    Metric.tendsto_atTop.mp hαsqsum.tendsto_atTop_zero.sqrt ε hεpos
  refine ⟨B₁ / 2, B₄ + B₅, ?hB₁pos, ?hB₂pos, ?hB⟩
  case hB =>
    refine ⟨n₀, ?hn₀⟩
    case hn₀ =>
      apply Eventually.mono (hC₃.and hC₄)
      intro ω hω n hn
      obtain ⟨hC₃, hC₄⟩ := hω
      have hα := hn₀ n hn
      have hαnpos : 0 < α n := by apply hαpos
      simp at hα
      rw [Real.sqrt_sq hαnpos.le] at hα
      rw [abs_of_nonneg hαnpos.le] at hα

      set x := fun n => x n ω
      set e₁ := fun n => e₁ (n + 1) ω
      set e₂ := fun n => e₂ (n + 1) ω
      have hineq : ∀ n, φ (x (n + 1) - z) ≤
        (1 - B₁ * α n + B₂ * α n ^ 2 + B₃ * (α n) ^ 4) * φ (x n - z) +
        ⟪φ' (x n - z), e₁ n⟫ + B₄ * (α n) ^ 2 + B₅ * (α n) ^ 4 := by
        intro n
        have : 0 < α n := by apply hαpos
        have hineq := hL (x n - z) (x (n + 1) - z)
        simp at hineq

        have : x (n + 1) - x n =
          (α n) • (f (x n) - x n) + e₁ n + e₂ n := by
          rw [sub_eq_iff_eq_add]
          move_add [←x n]
          exact hx.step n ω
        apply hineq.trans
        rw [this, inner_add_right, inner_add_right, inner_smul_right]
        grw [hdecrease (x n)]
        have : f (x n) - x n = (f (x n) - z) + (z - x n) := by simp
        rw [this]
        grw [norm_add_sq_le_norm_sq_add_norm_sq]
        grw [norm_add_sq_le_norm_sq_add_norm_sq]
        rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (hαpos n).le]
        grw [norm_add_sq_le_norm_sq_add_norm_sq]
        have : f (x n) - z = f (x n) - f z := by
          conv_lhs => rw [hz]
        rw [this]
        grw [hfLip (x n) z]
        conv_lhs =>
          pattern z - x n
          rw [←neg_sub]
        rw [norm_neg, mul_pow]
        grw [hC₀ (x n - z)]
        grw [hC₆ (x n - z) (e₂ n)]
        grw [hC₁ (e₂ n)]
        grw [hC₃ n]
        grw [hC₄ n]
        grw [hC₅ (x n)]
        simp_rw [mul_pow]
        grw [add_sq_le]
        simp_rw [Real.sq_sqrt (hEnergy.nonneg (x n - z))]
        simp_rw [←mul_assoc, mul_add, ←add_assoc]
        simp_rw [←mul_assoc]
        simp
        have : C₆ * √(φ (x n - z)) * C₁ * C₄ * α n ^ 2 * C₅ * √(φ (x n - z))
          = C₆ * C₁ * C₄ * C₅ * (α n) ^ 2 * φ (x n - z) := by
          rw [mul_comm]
          rw [←mul_comm (√(φ (x n - z)))]
          simp_rw [←mul_assoc]
          rw [Real.mul_self_sqrt (hEnergy.nonneg (x n - z))]
          ring
        rw [this]
        have sqrt_le : √(φ (x n - z)) ≤ 1 + φ (x n - z) := by
          set s := √(φ (x n - z)) with hs_def
          have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
          have hs_sq : s ^ 2 = φ (x n - z) := Real.sq_sqrt (hEnergy.nonneg _)
          have hsq := sq_nonneg (s - 1)
          rw [sub_sq, hs_sq, one_pow, mul_one] at hsq
          nlinarith [sq_nonneg s]
        grw [sqrt_le]
        simp_rw [mul_comm C₆]
        simp_rw [add_mul, ←add_assoc]
        simp_rw [←pow_mul]
        simp
        simp_rw [←neg_mul]

        simp_rw [mul_right_comm (b := α n ^ 2)]
        simp_rw [mul_right_comm (b := α n ^ 4)]
        simp_rw [mul_comm (φ (x n - z)), mul_right_comm (b := φ (x n - z))]

        apply le_of_eq
        ring

      grw [hineq n]
      have : α n ^ 4 ≤ α n ^ 2 := by
        apply pow_le_pow_of_le_one
        linarith
        exact (le_min_iff.mp hα.le).1
        simp
      grw [this]
      have : 1 - B₁ * α n + B₂ * α n ^ 2 + B₃ * α n ^ 2 ≤ 1 - B₁ / 2 * α n := by
        have : α n ^ 2 ≤ α n * ε := by
          rw [pow_two]
          apply mul_le_mul_of_nonneg_left hα.le hαnpos.le
        grw [this]
        simp_rw [←mul_assoc, mul_right_comm (b := α n)]
        rw [add_assoc, ←add_mul]
        have : B₂ * ε + B₃ * ε ≤ B₁ / 2 := by
          rw [←add_mul]
          have := min_le_right 1 (B₁ / (2 * (B₂ + B₃ + 1)))
          unfold ε
          grw [this]
          rw [←mul_div_assoc, mul_comm, mul_div_mul_comm]
          conv_rhs => rw [←mul_one (B₁ / 2)]
          apply mul_le_mul_of_nonneg_left
          apply (div_le_comm₀ _ _).mpr
          simp
          linarith
          simp
          linarith
        grw [this]
        apply le_of_eq
        ring

      grw [this]
      apply le_of_eq
      ring
      exact hEnergy.nonneg (x n - z)
      exact hEnergy.nonneg (x n - z)
  linarith
  positivity

end StochasticApproximation
