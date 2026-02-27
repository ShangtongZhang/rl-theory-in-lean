import Mathlib

/-- `linear_bound_close` closes goals of the form `a ≤ C * (‖x‖ + 1)` or `a ≤ C * ‖x‖ + D`
    that arise after norm decomposition, by normalising with `ring_nf` and then dispatching
    via a combination of `gcongr`, `linarith`, and `positivity`. --/
macro "linear_bound_close" : tactic =>
  `(tactic|
    (ring_nf
     first
       | linarith
       | (apply add_le_add <;> (first | linarith | positivity | gcongr))
       | (apply mul_le_mul_of_nonneg_right <;> (first | linarith | positivity))
       | (apply mul_le_mul_of_nonneg_left  <;> (first | linarith | positivity))
       | positivity))
