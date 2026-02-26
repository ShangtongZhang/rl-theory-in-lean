import Mathlib

/-- Reduces ‖∑ i, f i‖ ≤ ? to per-element bounds by chaining
    norm_sum_le → Finset.sum_le_sum → intro of index and membership. --/
macro "norm_sum_intro" : tactic =>
  `(tactic| (
    apply le_trans (norm_sum_le _ _)
    apply Finset.sum_le_sum
    intro _ _
  ))
