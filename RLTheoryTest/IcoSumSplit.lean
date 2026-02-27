import Mathlib
import RLTheory.Tactic.IcoSumSplit

-- one example that uses `ico_sum_split` as a proof step
example : ∑ i ∈ Finset.Ico 0 10, i = ∑ i ∈ Finset.Ico 0 5, i + ∑ i ∈ Finset.Ico 5 10, i := by
  ico_sum_split 5
