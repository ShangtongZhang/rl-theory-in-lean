import Mathlib

/-- `norm_bound_positivity` closes `0 ≤ e` (or `0 < e`) goals that arise as
    bound non-negativity side-conditions. It tries `positivity` first, then
    collects all local hypotheses of the form `0 ≤ h` or `0 < h` and forwards
    them to `linarith`, and finally tries `norm_num`. -/
macro "norm_bound_positivity" : tactic =>
  `(tactic| (
    first
    | positivity
    | linarith
    | norm_num
    | (apply mul_nonneg; first | positivity | linarith; first | positivity | linarith)
    | (apply add_nonneg; first | positivity | linarith; first | positivity | linarith)))
