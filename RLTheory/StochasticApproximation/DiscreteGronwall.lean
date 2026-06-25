/-
SPDX-License-Identifier: MIT
SPDX-FileCopyrightText: 2025 Shangtong Zhang <shangtong.zhang.cs@gmail.com>
-/
import RLTheory.Defs

open Real Finset

namespace StochasticApproximation

variable {u b c : ℕ → ℝ}

theorem discrete_gronwall_aux
  {n₀ : ℕ}
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0) :
  ∀ n, n₀ ≤ n → u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
  ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) := by
  intro n hn
  refine Nat.le_induction ?base ?succ n hn
  case base => simp
  case succ =>
    intro k hk ih
    grw [hu k (by linarith), ih]
    rw [mul_add, mul_comm, mul_assoc, prod_Ico_mul_eq_prod_Ico_add_one,
      add_assoc]
    simp
    rw [mul_sum, ←sum_Ico_add_eq_sum_Ico_add_one]
    simp
    apply sum_le_sum
    intro i hi
    rw [mul_comm, mul_assoc, prod_Ico_mul_eq_prod_Ico_add_one]
    simp at hi
    omega
    simpa
    simpa
    have := hc k (by linarith)
    linarith

theorem discrete_gronwall
  {n₀ : ℕ}
  (hun₀ : 0 ≤ u n₀)
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0)
  (hb : ∀ n ≥ n₀, b n ≥ 0) :
  ∀ n, n₀ ≤ n →
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
  intro n hn
  grw [discrete_gronwall_aux hu hc n hn]
  have hk : ∀ k ∈ Ico n₀ n, ∏ i ∈ Ico (k + 1) n, (1 + c i) ≤
    ∏ i ∈ Ico n₀ n, (1 + c i) := by
    intro k hk
    simp at hk
    nth_rw 2 [←prod_Ico_consecutive (n := k + 1)]
    have : 0 < ∏ i ∈ Ico (k + 1) n, (1 + c i) := by
      apply prod_pos
      intro i hi
      simp at hi
      linarith [hc i (by linarith)]
    simp [this]
    have : 1 = ∏ i ∈ Ico n₀ (k + 1), (1 : ℝ) := by simp
    nth_rw 1 [this]
    apply prod_le_prod
    simp
    intro i hi
    simp at hi
    simp
    apply hc i (by linarith)
    omega
    omega
  apply LE.le.trans
  apply add_le_add_left
  apply sum_le_sum
  intro j hj
  simp at hj
  grw [hk]
  apply hb j (by linarith)
  simpa
  rw [←sum_mul, ←add_mul]
  apply mul_le_mul_of_nonneg_left
  grw [prod_le_prod (g := fun i => exp (c i))]
  simp [exp_sum]
  intro i hi
  simp at hi
  apply add_nonneg; simp; apply hc i (by linarith)
  intro i hi
  simp [add_comm, add_one_le_exp]
  apply add_nonneg
  simpa
  apply sum_nonneg
  intro i hi
  simp at hi
  apply hb i (by linarith)

theorem discrete_gronwall_Ico
  {n₀ n₁ : ℕ}
  (hun₀ : 0 ≤ u n₀)
  (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
  (hc : ∀ n ≥ n₀, c n ≥ 0)
  (hb : ∀ n ≥ n₀, b n ≥ 0) :
  ∀ n ∈ Ico n₀ n₁,
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) := by
  intro n hn
  simp at hn
  grw [discrete_gronwall hun₀ hu hc hb n hn.1]
  apply mul_le_mul
  simp
  apply sum_le_sum_of_subset_of_nonneg
  apply Ico_subset_Ico_right
  omega
  intro i hi _
  simp at hi
  exact hb i (by linarith)
  simp
  apply sum_le_sum_of_subset_of_nonneg
  apply Ico_subset_Ico_right
  omega
  intro i hi _
  simp at hi
  exact hc i (by linarith)
  positivity
  apply add_nonneg
  simpa
  apply sum_nonneg
  intro i hi
  simp at hi
  exact hb i (by linarith)

end StochasticApproximation
