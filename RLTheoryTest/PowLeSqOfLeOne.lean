import Mathlib
import RLTheory.Tactic.PowLeSqOfLeOne

-- one example that uses `pow_le_sq_of_le_one` as a proof step
example (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : a ^ 4 ≤ a ^ 2 := by
  pow_le_sq_of_le_one
