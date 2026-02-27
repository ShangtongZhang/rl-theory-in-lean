import Mathlib

/-- Repeatedly decomposes norm expressions in the goal by applying `norm_add_le`,
    `norm_sub_le`, `norm_smul`, and `norm_neg` in any order until no further
    progress can be made, reducing composite ‖·‖ terms to sums of simpler norms. --/
macro "norm_decomp" : tactic =>
  `(tactic|
    repeat (first
      | grw [norm_add_le]
      | grw [norm_sub_le]
      | rw [norm_smul]
      | rw [norm_neg]))
