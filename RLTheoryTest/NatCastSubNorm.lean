import Mathlib
import RLTheory.Tactic.NatCastSubNorm

-- Demonstrate nat_cast_sub_norm: rewrite ((n - 1 : ℕ) : ℝ) into (n : ℝ) - 1
example (n : ℕ) (hn : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  nat_cast_sub_norm
