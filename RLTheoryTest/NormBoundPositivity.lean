import Mathlib
import RLTheory.Tactic.NormBoundPositivity

-- one example that uses `norm_bound_positivity` as a proof step
example (x : ℝ) : 0 ≤ ‖x‖ := by
  norm_bound_positivity
