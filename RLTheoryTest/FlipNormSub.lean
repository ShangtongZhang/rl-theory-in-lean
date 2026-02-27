import Mathlib
import RLTheory.Tactic.FlipNormSub

-- one example that uses `flip_norm_sub` as a proof step
example (a b : ℝ) : ‖a - b‖ = ‖b - a‖ := by
  flip_norm_sub a, b
