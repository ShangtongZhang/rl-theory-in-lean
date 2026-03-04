import Mathlib
import RLTheory.Tactic.AbsNonnegFactorSimp

-- Example demonstrating abs_nonneg_factor_simp: simplifies |c * x| → c * |x| when c is nonneg
example (c x : ℝ) (hc : 0 ≤ c) : |c * x| = c * |x| := by
  abs_nonneg_factor_simp
