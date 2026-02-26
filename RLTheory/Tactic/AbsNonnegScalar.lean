import Mathlib

/-- `abs_nonneg_scalar` rewrites `|c * e|` to `c * |e|` and `|c|` to `c`
    throughout the goal whenever the non-negativity of `c` can be established
    by `positivity`, a hypothesis, or `linarith`. -/
macro "abs_nonneg_scalar" : tactic =>
  `(tactic|
    (simp only [abs_mul]
     try simp only [abs_of_nonneg (by positivity)]
     try simp only [abs_of_nonneg (by linarith)]
     try simp only [abs_of_nonneg (by assumption)]
     try norm_num))
