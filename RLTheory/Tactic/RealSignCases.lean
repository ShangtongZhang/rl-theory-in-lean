import Mathlib

/-- `real_sign_cases x` splits on the sign of a real term `x` (positive,
    zero, or negative) and automatically rewrites `Real.sign` and `|·|`
    in every branch. -/
syntax "real_sign_cases" term : tactic

macro_rules
  | `(tactic| real_sign_cases $x) =>
    `(tactic| (
        rcases lt_trichotomy ($x : ℝ) 0 with _hneg | _hzero | _hpos <;>
        simp [Real.sign_of_pos, Real.sign_of_neg, Real.sign_zero,
              abs_of_pos, abs_of_neg, abs_zero, *]))
