import Mathlib
import RLTheory.Tactic.LinearBoundClose

-- one example that uses `linear_bound_close` as a proof step
example (x C : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (h : x ≤ C * x + C) :
    x ≤ C * (x + 1) := by
  linear_bound_close
