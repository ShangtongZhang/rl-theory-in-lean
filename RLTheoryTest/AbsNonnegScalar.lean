import Mathlib
import RLTheory.Tactic.AbsNonnegScalar

-- Demonstrate abs_nonneg_scalar: rewrites |c * e| to c * |e| when c ≥ 0
example (c x : ℝ) (hc : 0 ≤ c) : |c * x| = c * |x| := by
  abs_nonneg_scalar
