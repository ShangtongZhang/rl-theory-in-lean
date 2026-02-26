import Mathlib

/-- Rewrites |⟪v, a⟫ - ⟪v, b⟫| to |⟪v, a - b⟫| via linearity
    and then applies the Cauchy-Schwarz norm bound. --/
macro "inner_sub_cauchy" : tactic =>
  `(tactic| first
    | (rw [← inner_sub_right]; apply abs_real_inner_le_norm)
    | (rw [← inner_sub_left]; apply abs_real_inner_le_norm)
    | (apply le_trans _ (abs_real_inner_le_norm _ _);
       congr 1; rw [← inner_sub_right])
    | (apply le_trans _ (abs_real_inner_le_norm _ _);
       congr 1; rw [← inner_sub_left]))
