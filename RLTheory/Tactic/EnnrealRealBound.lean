import Mathlib

/-- `ennreal_real_bound` converts a goal or hypothesis relating an `ENNReal` expression
    to a real-valued bound. It applies `ENNReal.ofReal_le_ofReal` to reduce an
    `ENNReal.ofReal a ≤ ENNReal.ofReal b` goal to `a ≤ b`, optionally using
    `ENNReal.ofReal_toReal` and `ENNReal.ofReal_eq_coe_nnreal` to normalise further. -/
syntax "ennreal_real_bound" (" at " ident)? : tactic

macro_rules
  | `(tactic| ennreal_real_bound) =>
    `(tactic| (first
      | (apply ENNReal.ofReal_le_ofReal; assumption)
      | (apply ENNReal.ofReal_le_ofReal; linarith)
      | (apply ENNReal.ofReal_le_ofReal; positivity)
      | skip))
  | `(tactic| ennreal_real_bound at $h:ident) =>
    `(tactic| (have := ENNReal.ofReal_le_ofReal $h
               exact this))
