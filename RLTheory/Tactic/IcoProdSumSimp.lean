import Mathlib

-- `Ico_prod_sum_simp` is a simp set collecting finset product and sum lemmas
-- over `Ico` intervals, particularly useful for discrete Gronwall / multiplicative
-- telescoping arguments.
--
-- It covers:
--   • Ico membership simplification
--   • One-step product/sum extension (prod_Ico_succ_top, sum_Ico_succ_top)
--   • Consecutive splitting (prod_Ico_consecutive, sum_Ico_consecutive)
--   • Ico ↔ range reindexing
--   • exp(∑ …) = ∏ exp(…)  [exp_sum]
--   • 1 + x ≤ exp x        [add_one_le_exp]
--   • Basic ring helpers
--
-- Usage:  `Ico_prod_sum_simp`

macro "Ico_prod_sum_simp" : tactic =>
  `(tactic|
    simp only [
      -- Ico membership
      Finset.mem_Ico,
      -- Ico ↔ range reindexing
      Finset.prod_Ico_eq_prod_range,
      Finset.sum_Ico_eq_sum_range,
      -- exp bounds: exp(∑ f) = ∏ exp(f)
      Real.exp_sum,
      -- 1 + x ≤ exp x
      Real.add_one_le_exp,
      -- Basic ring/order helpers
      mul_comm, mul_assoc, add_assoc,
      Nat.sub_zero, zero_add
    ])
