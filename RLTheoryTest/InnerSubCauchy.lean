import Mathlib
import RLTheory.Tactic.InnerSubCauchy

-- one example that uses `inner_sub_cauchy` as a proof step
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

example (v a b : E) :
    abs (@inner ℝ E _ v a - @inner ℝ E _ v b) ≤ ‖v‖ * ‖a - b‖ := by
  inner_sub_cauchy
