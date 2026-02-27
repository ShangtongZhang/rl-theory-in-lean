import Mathlib
open Real

/-- `sqrt_norm_bound` normalises goals involving `Real.sqrt` and norm bounds
    by rewriting with `Real.sq_sqrt`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`,
    and dispatching non-negativity via `positivity`. -/
macro "sqrt_norm_bound" : tactic =>
  `(tactic| (
    simp only [Real.sqrt_sq (by positivity), Real.sq_sqrt (by positivity)] at *
    try rw [Real.sqrt_sq (by positivity)]
    try rw [Real.sqrt_sq (by positivity)] at *
    try (apply Real.sqrt_le_sqrt; positivity)
    try positivity
    try linarith
    try nlinarith [Real.sqrt_nonneg _]))
