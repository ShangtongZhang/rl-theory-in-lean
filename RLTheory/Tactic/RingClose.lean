import Mathlib

/-- `ring_close` normalises the goal with `ring_nf` and then tries
    `rfl`, `norm_num`, and `linarith` to close it.
    Using `try` ensures success when `ring_nf` already closes the goal. -/
macro "ring_close" : tactic =>
  `(tactic| (ring_nf; try (first | rfl | norm_num | linarith)))
