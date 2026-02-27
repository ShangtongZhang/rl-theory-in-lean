import Mathlib
import RLTheory.Tactic.NormLinearGrowthClose

-- one example that uses `norm_linear_growth_close` as a proof step
-- Demonstrates the tactic on a linear-growth bound: ‖u - v‖ ≤ 6 * (‖v‖ + 1)
-- given individual growth bounds, closed via triangle inequality then linarith.
example (u v : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ ≤ 3 * (‖v‖ + 1)) (hv : ‖v‖ ≤ 3 * (‖v‖ + 1)) :
    ‖u - v‖ ≤ 6 * (‖v‖ + 1) := by
  norm_linear_growth_close
