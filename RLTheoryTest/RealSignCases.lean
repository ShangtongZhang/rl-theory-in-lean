import Mathlib
import RLTheory.Tactic.RealSignCases

-- Demonstrate that real_sign_cases splits on sign and simplifies sign/abs expressions
example (x : ℝ) : Real.sign x * |x| = x := by
  real_sign_cases x
