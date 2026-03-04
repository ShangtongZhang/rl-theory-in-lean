import Mathlib
import RLTheory.Tactic.SumNonnegSearch

-- Demonstrate sum_nonneg_search: prove a sum over a range is nonneg
-- using a hypothesis that the summand is nonneg.
example (n : ℕ) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ ∑ _i ∈ Finset.range n, a := by
  sum_nonneg_search
