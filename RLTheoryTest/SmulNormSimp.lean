import Mathlib
import RLTheory.Tactic.SmulNormSimp

-- Test that smul_norm_simp normalizes sub_sub_sub_comm instances
example (a b c d : ℝ) : a - b - (c - d) = a - c - (b - d) := by
  smul_norm_simp
