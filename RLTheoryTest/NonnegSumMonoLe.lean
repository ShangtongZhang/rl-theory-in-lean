import Mathlib
import RLTheory.Tactic.NonnegSumMonoLe

-- Demonstrate `nonneg_sum_mono_le` on a concrete example:
-- the sum of squares over Ico 0 n is ≤ the sum over Ico 0 m when n ≤ m.
example (n m : ℕ) (hnm : n ≤ m) : ∑ i ∈ Finset.Ico 0 n, (i : ℝ) ^ 2 ≤ ∑ i ∈ Finset.Ico 0 m, (i : ℝ) ^ 2 := by
  nonneg_sum_mono_le
