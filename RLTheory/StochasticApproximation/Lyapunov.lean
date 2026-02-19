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

import Mathlib.Data.Real.Sign
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

import RLTheory.Defs
import RLTheory.Analysis.Normed.Group.Basic
import RLTheory.StochasticApproximation.LpSpace

open ENNReal NNReal Real Finset Filter Asymptotics RLTheory
open scoped Topology InnerProductSpace RealInnerProductSpace Gradient


namespace StochasticApproximation

variable {d : ℕ}

class LyapunovCandidate (φ : E d → ℝ) (φ' : E d → E d) where
  nonneg :  ∀ x, 0 ≤ φ x
  zero : ∀ z, z = 0 ↔ φ z = 0
  smooth :
    ∃ L, 0 ≤ L ∧ ∀ (x y : E d), φ y ≤ φ x + ⟪φ' x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2
  inner_grad_eq : ∃ C, 0 ≤ C ∧ ∀ x, ⟪φ' x, x⟫ = C * φ x
  inner_grad_le' : ∃ C, 0 ≤ C ∧ ∀ x y,
    ∑ i, |φ' x i| * |y i| ≤ C * √(φ x) * √(φ y)
  norm_le : ∃ C, 0 ≤ C ∧ ∀ x, ‖x‖ ≤ C * √(φ x)
  le_norm : ∃ C, 0 ≤ C ∧ ∀ x, √(φ x) ≤ C * ‖x‖

lemma LyapunovCandidate.inner_grad_le {φ : E d → ℝ} {φ' : E d → E d}
  (h : LyapunovCandidate φ φ') :
  ∃ C, 0 ≤ C ∧ ∀ x y, ⟪φ' x, y⟫ ≤ C * √(φ x) * √(φ y) := by
  obtain ⟨C, hCpos, hC⟩ := h.inner_grad_le'
  use C
  use hCpos
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply LE.le.trans ?_ (hC x y)
  apply sum_le_sum
  intro i hi
  rw [mul_comm, ←abs_mul]
  apply le_of_abs_le
  rfl

class DecreaseAlong (φ : E d → ℝ) (φ' : E d → E d) (f : E d → E d) where
  decrease : ∃ η, 0 < η ∧ ∀ z, z = f z →
    ∀ x, ⟪φ' (x - z), f x - x⟫ ≤ - η * φ (x - z)

class LyapunovFunction (φ : E d → ℝ) (φ' : E d → E d) (f : E d → E d) extends
  LyapunovCandidate φ φ', DecreaseAlong φ φ' f

-- LyapunovCandidate for LpSpace (generalized version)
class LyapunovCandidateLp {p : ℕ} [Fact (1 ≤ (p : ℝ≥0∞))]
    (φ : LpSpace p d → ℝ) (φ' : LpSpace p d → LpSpace p d) where
  nonneg :  ∀ x, 0 ≤ φ x
  zero : ∀ z, z = 0 ↔ φ z = 0
  smooth :
    ∃ L, 0 ≤ L ∧ ∀ (x y : LpSpace p d), φ y ≤ φ x + ⟪toL2 (φ' x), toL2 (y - x)⟫ + L / 2 * ‖toL2 (y - x)‖ ^ 2
  inner_grad_eq : ∃ C, 0 ≤ C ∧ ∀ x, ⟪toL2 (φ' x), toL2 x⟫ = C * φ x
  inner_grad_le' : ∃ C, 0 ≤ C ∧ ∀ x y,
    ∑ i, |φ' x i| * |y i| ≤ C * √(φ x) * √(φ y)
  norm_le : ∃ C, 0 ≤ C ∧ ∀ x, ‖toL2 x‖ ≤ C * √(φ x)
  le_norm : ∃ C, 0 ≤ C ∧ ∀ x, √(φ x) ≤ C * ‖x‖

lemma lyapunovCandidateLp_half_sq_Lp {p : ℕ} (hp : 2 ≤ p) :
    haveI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by simp; linarith⟩
    LyapunovCandidateLp (@half_sq_Lp p d) (@half_sq_Lp' p d) := by
  haveI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by simp; linarith⟩
  refine {
    nonneg := ?nonneg
    zero := ?zero
    smooth := ?smooth
    inner_grad_eq := ?inner_grad_eq
    inner_grad_le' := ?inner_grad_le'
    norm_le := ?norm_le
    le_norm := ?le_norm
  }
  case nonneg =>
    intro x; simp [half_sq_Lp]
  case zero =>
    intro x; unfold half_sq_Lp; simp
  case inner_grad_eq =>
    use 2
    simp
    intro x
    have := inner_gradient_half_sq_Lp_self (p := p) (by linarith) x
    rw [this, half_sq_Lp]
    ring
  case inner_grad_le' =>
    use 2
    simp
    intro x y
    have := inner_abs_gradient_half_sq_Lp_le (p := p) (by linarith) x y
    grw [this]
    simp_rw [half_sq_Lp]
    apply le_of_eq
    simp
    ring_nf
    simp
  case norm_le =>
    have := L2_le_Lp (d := d) (hp := by linarith)
    obtain ⟨C, hCnonneg, hC⟩ := this
    refine ⟨√2 * C, (by positivity), ?hC⟩
    intro x
    have h_eq : C * ‖x‖ = √2 * C * √(half_sq_Lp x) := by
      simp only [half_sq_Lp]
      have h1 : (1 : ℝ) / 2 * ‖x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by ring
      rw [h1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      have h2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
      field_simp
    calc ‖toL2 x‖ ≤ C * ‖x‖ := hC x
      _ = √2 * C * √(half_sq_Lp x) := h_eq
  case le_norm =>
    use (√2)⁻¹
    simp
    intro x
    -- Goal: √(half_sq_Lp x) ≤ (√2)⁻¹ * ‖x‖
    -- half_sq_Lp x = 1/2 * ‖x‖^2, so √(half_sq_Lp x) = ‖x‖ / √2
    simp only [half_sq_Lp]
    have h1 : (1 : ℝ) / 2 * ‖x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by ring
    rw [h1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    rw [div_eq_mul_inv, mul_comm]
  case smooth =>
    use (p - 1)
    constructor
    simp; linarith
    intro x y
    have := smooth_half_sq_Lp (p := p) (by linarith) x y
    grw [this]
    simp [toL2, half_sq_Lp]
    grw [Lp_le_L2]
    apply le_of_eq
    simp [toL2]
    ring_nf
    simp; linarith
    linarith

-- Special case for p = 2 where LpSpace 2 d = E d (definitionally equal)
-- This allows direct use without wrappers
lemma lyapunovCandidate_half_sq_L2 :
    LyapunovCandidate (@half_sq_Lp 2 d) (@half_sq_Lp' 2 d) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  constructor
  case nonneg =>
    intro x; simp [half_sq_Lp]
  case zero =>
    intro x; unfold half_sq_Lp; simp
  case inner_grad_eq =>
    use 2
    simp
    intro x
    have := inner_gradient_half_sq_Lp_self (p := 2) (by linarith) x
    simp only [toL2, WithLp.toLp_ofLp] at this
    rw [this, half_sq_Lp]
    ring
  case inner_grad_le' =>
    use 2
    simp
    intro x y
    have := inner_abs_gradient_half_sq_Lp_le (p := 2) (by linarith) x y
    grw [this]
    simp_rw [half_sq_Lp]
    apply le_of_eq
    simp
    ring_nf
    simp
  case norm_le =>
    refine ⟨√2, (by positivity), ?hC⟩
    intro x
    simp only [half_sq_Lp]
    have h1 : (1 : ℝ) / 2 * ‖x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by ring
    rw [h1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have h2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
    field_simp
    rfl
  case le_norm =>
    use (√2)⁻¹
    simp
    intro x
    simp only [half_sq_Lp]
    have h1 : (1 : ℝ) / 2 * ‖x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by ring
    rw [h1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    rw [div_eq_mul_inv, mul_comm]
  case smooth =>
    use 1
    constructor
    simp
    intro x y
    have := smooth_half_sq_Lp (p := 2) (by linarith) x y
    simp only [toL2, WithLp.toLp_ofLp] at this
    grw [this]
    simp [half_sq_Lp]
    apply le_of_eq
    ring_nf

end StochasticApproximation
