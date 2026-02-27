import Mathlib

/-- `norm_sq_inner_simp` rewrites every `‖v‖^2` (or `‖v‖ * ‖v‖`) subterm in the goal
    to the real inner product `⟪v, v⟫_ℝ` using `real_inner_self_eq_norm_sq`
    (and `norm_sq_eq_re_inner` for the RCLike setting), then strips away any
    `RCLike.re` wrappers via `RCLike.re_to_real`, leaving a clean inner-product goal. --/
macro "norm_sq_inner_simp" : tactic =>
  `(tactic| (
    simp only [
      norm_sq_eq_re_inner (𝕜 := ℝ),
      ← real_inner_self_eq_norm_sq,
      RCLike.re_to_real,
      ← sq]
    try ring_nf))
