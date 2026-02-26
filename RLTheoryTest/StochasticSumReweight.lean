import Mathlib
import RLTheory.Tactic.StochasticSumReweight

-- Demonstrates stochastic_sum_reweight: rewrites the constant upper bound C
-- as (∑ i, w i) * C, then distributes via sum_mul and applies sum_le_sum.
example (n : ℕ) (w : Fin n → ℝ) (f : Fin n → ℝ) (C : ℝ)
    (hw : ∑ i, w i = 1)
    (hwnn : ∀ i, 0 ≤ w i)
    (hf : ∀ i, f i ≤ C) :
    ∑ i, w i * f i ≤ C := by
  stochastic_sum_reweight hw
  intro i _
  exact mul_le_mul_of_nonneg_left (hf i) (hwnn i)
