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
import RLTheory.Data.Real.Basic
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
  simp
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

lemma lyapunovCandidate_half_sq_Lp {p : ℕ} (hp : 2 ≤ p) :
  LyapunovCandidate (@half_sq_Lp p d) (@half_sq_Lp' p d) := by
  have : Fact (1 ≤ (p : ℝ≥0∞)) := by apply Fact.mk (by simp; linarith)
  constructor
  case nonneg =>
    intro x; simp [half_sq_Lp]
  case zero =>
    intro x; unfold half_sq_Lp; simp
  case inner_grad_eq =>
    use 2
    simp
    intro x
    have := inner_gradient_half_sq_Lp_self (p := p) (by linarith) x
    simp [toL2] at this
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
    simp [toL2] at hC
    grw [hC]
    simp [half_sq_Lp]
    ring_nf
    simp
  case le_norm =>
    use (√2)⁻¹
    simp
    intro x
    simp [half_sq_Lp]
    apply Lp_le_L2
    linarith
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

end StochasticApproximation
