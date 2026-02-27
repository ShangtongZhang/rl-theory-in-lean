import Mathlib

/-- Normalises goals containing ‖c • v‖ or ‖c • (a - b)‖ by applying `norm_smul`,
    rewriting `‖c‖` to `|c|` via `Real.norm_eq_abs`, then discharging `0 ≤ c`
    (and hence `|c| = c`) using `positivity`, `linarith`, or `assumption`,
    leaving a purely arithmetic residual for `ring_nf`/`linarith`. --/
macro "norm_smul_expand" : tactic =>
  `(tactic|
    (simp only [norm_smul, Real.norm_eq_abs]
     first
       | simp only [abs_of_nonneg (by positivity)]
       | simp only [abs_of_nonneg (by linarith)]
       | simp only [abs_of_nonneg (by assumption)]
       | skip
     try ring_nf
     try linarith))
