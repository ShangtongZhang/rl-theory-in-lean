import Mathlib

/-- `split_abs_le` splits a goal of the form `|a| ≤ b` into two subgoals `-b ≤ a` and `a ≤ b`
    via `abs_le.mpr` + `constructor`, then attempts to close each branch automatically. -/
macro "split_abs_le" : tactic =>
  `(tactic|
    (apply abs_le.mpr
     constructor
     all_goals (first
       | linarith
       | (ring_nf; linarith)
       | (simp only [abs_of_nonneg, abs_of_nonpos, neg_sub]; linarith)
       | skip)))
