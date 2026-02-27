import Mathlib
import RLTheory.Tactic.RingSimpClose

-- Demonstrate ring_simp_close closing an equality goal that becomes trivial
-- after ring normalization, a concrete instance of its intended use.
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring_simp_close
