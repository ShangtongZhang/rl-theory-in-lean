import Mathlib

/-- Simp macro: fold abs_mul + abs_of_nonneg/pos for a nonneg scalar.
    Simplifies expressions of the form `|c * x|`, `|x * c|`, `|c|`
    where `c` is nonneg or pos in context, rewriting to `c * |x|`. -/
macro "abs_nonneg_factor_simp" : tactic =>
  `(tactic| (simp only [abs_mul, abs_of_nonneg, abs_of_pos, *] <;>
    try norm_num <;>
    try positivity))
