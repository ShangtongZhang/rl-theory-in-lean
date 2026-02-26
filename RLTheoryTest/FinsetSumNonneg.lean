import Mathlib
import RLTheory.Tactic.FinsetSumNonneg

-- Demonstrate `finset_sum_nonneg` on a concrete Ico sum whose summands are
-- nonneg by `positivity` (squares of natural numbers cast to ℝ).
example (n : ℕ) : 0 ≤ ∑ i ∈ Finset.Ico 0 n, (i : ℝ) ^ 2 := by
  finset_sum_nonneg
