import Mathlib

/-- Rewrites ‖a • v - b • v‖ into |a - b| * ‖v‖ by
    combining ← sub_smul with norm_smul in one step. --/
macro "sub_smul_norm_expand" : tactic =>
  `(tactic| (
    rw [← sub_smul, norm_smul]
  ))
