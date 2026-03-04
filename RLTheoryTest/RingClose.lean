import Mathlib
import RLTheory.Tactic.RingClose

-- Demonstrate ring_close: normalize and close a polynomial equality
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring_close
