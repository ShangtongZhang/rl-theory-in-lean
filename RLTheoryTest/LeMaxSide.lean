import Mathlib
import RLTheory.Tactic.LeMaxSide

-- Example demonstrating le_max_side on a nested max expression
example (a b c : ℝ) : a ≤ max (max a b) c := by
  le_max_side
