import Mathlib

/-- `sqrt_norm_simp` normalises sub-expressions of the form `√(‖x‖^2 / c)`, `√(‖x‖^2)`,
    `‖x‖ / √c`, and similar sqrt-norm combinations by applying the standard
    `Real.sqrt_div`, `Real.sqrt_sq`, `Real.sqrt_mul_self`, and related lemmas,
    then optionally calling `field_simp` and `ring` to finish. --/
macro "sqrt_norm_simp" : tactic =>
  `(tactic| (
    simp only [
      Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul_self (norm_nonneg _),
      Real.sqrt_inv]
    try field_simp
    try ring
    try rw [div_eq_mul_inv, mul_comm]))
