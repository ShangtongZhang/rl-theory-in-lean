import Mathlib

/-- Closes goals of the form `0 ≤ ∑ i ∈ s, f i * g i ^ 2` (or `0 ≤ ∑ i, f i * g i ^ 2`)
    by applying `Finset.sum_nonneg`, then `mul_nonneg` on each summand,
    discharging the weight nonnegativity via `positivity`, `linarith`, or `assumption`,
    and the square nonnegativity via `positivity`. --/
macro "weighted_sq_nonneg" : tactic =>
  `(tactic| (
    apply Finset.sum_nonneg
    intro _ _
    apply mul_nonneg
    · first | positivity | linarith | assumption
    · positivity))
