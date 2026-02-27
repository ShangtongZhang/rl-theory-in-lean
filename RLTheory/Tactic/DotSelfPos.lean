import Mathlib

/-- Closes goals of the form `0 < x ⬝ᵥ x` (or `0 < ⟪x, x⟫_ℝ`) for a real vector `x`
    by searching the local context for a hypothesis `x ≠ 0` and dispatching via
    `Matrix.dotProduct_star_self_pos_iff` (dot-product form) or
    `real_inner_self_eq_norm_sq` + `norm_pos_iff` (inner-product form). --/
macro "dot_self_pos" : tactic =>
  `(tactic|
    first
    | (have h := Matrix.dotProduct_star_self_pos_iff.mpr (by assumption)
       simp only [star_trivial] at h
       exact h)
    | (rw [real_inner_self_eq_norm_sq]
       exact sq_pos_of_pos (norm_pos_iff.mpr (by assumption))))
