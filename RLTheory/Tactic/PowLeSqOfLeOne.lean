import Mathlib

/-- `pow_le_sq_of_le_one` closes goals `a ^ n ≤ a ^ 2` (or `c * a ^ n ≤ c * a ^ 2`)
    when `0 ≤ a ≤ 1` is in context and `n ≥ 2`. -/
macro "pow_le_sq_of_le_one" : tactic =>
  `(tactic|
    first
    | (apply pow_le_pow_of_le_one <;> first | positivity | linarith | norm_num)
    | (apply mul_le_mul_of_nonneg_left _ (by positivity);
       apply pow_le_pow_of_le_one <;> first | positivity | linarith | norm_num))
