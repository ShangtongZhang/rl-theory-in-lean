import Mathlib
import RLTheory.Tactic.NormSmulExpand

-- one example that uses `norm_smul_expand` as a proof step
example (c : ℝ) (hc : 0 ≤ c) (v : ℝ) : ‖c • v‖ = c * ‖v‖ := by
  norm_smul_expand
