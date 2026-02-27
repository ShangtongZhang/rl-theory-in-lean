import Mathlib
import RLTheory.Tactic.SqrtNormSimp

-- Demonstrate sqrt_norm_simp simplifying √(‖x‖^2) to ‖x‖
example (x : ℝ) : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
  sqrt_norm_simp
