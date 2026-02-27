import Mathlib
import RLTheory.Tactic.SqrtNormBound

-- Demonstrate sqrt_norm_bound simplifying √(a²) ≤ √(b²) to a ≤ b, then closing via linarith
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) : Real.sqrt (a ^ 2) ≤ Real.sqrt (b ^ 2) := by
  sqrt_norm_bound
