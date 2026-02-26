import Mathlib
import RLTheory.Tactic.SubSmulNormExpand

-- one example that uses `sub_smul_norm_expand` as a proof step
example (a b : ℝ) (v : ℝ) : ‖a • v - b • v‖ = ‖a - b‖ * ‖v‖ := by
  sub_smul_norm_expand
