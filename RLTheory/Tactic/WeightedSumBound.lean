import Mathlib

macro "weighted_sum_bound" : tactic =>
  `(tactic|
    (apply Finset.sum_le_sum
     intro i _
     apply mul_le_mul_of_nonneg_left _ (by positivity)
     first | assumption | linarith | solve_by_elim |
       (apply le_ciSup (by exact bddAbove_range _))))
