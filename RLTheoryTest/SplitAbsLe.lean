import Mathlib
import RLTheory.Tactic.SplitAbsLe

-- Demonstrate split_abs_le on a simple concrete goal: |x| ≤ b when -b ≤ x and x ≤ b
example (x b : ℝ) (h1 : -b ≤ x) (h2 : x ≤ b) : |x| ≤ b := by
  split_abs_le
