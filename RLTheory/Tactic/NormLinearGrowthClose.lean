import Mathlib

/-- `norm_linear_growth_close` closes goals of the form `‖f w‖ ≤ C * (‖w‖ + 1)`
    (linear-growth bounds) that arise after extracting Lipschitz/growth constants.
    It applies `norm_smul` and `Real.norm_eq_abs` for scalar terms, simplifies
    absolute values for non-negative scalars via `abs_of_nonneg`, applies triangle
    inequalities (`norm_sub_le`, `norm_add_le`), then closes with `linarith` or `ring`. --/
macro "norm_linear_growth_close" : tactic =>
  `(tactic| (
    try simp only [norm_smul, Real.norm_eq_abs]
    try simp only [abs_of_nonneg (by positivity)]
    try simp only [abs_of_nonneg (by linarith)]
    try simp only [abs_of_nonneg (by assumption)]
    try (apply (norm_sub_le _ _).trans)
    try (apply (norm_add_le _ _).trans)
    try gcongr
    try linarith
    try ring))
