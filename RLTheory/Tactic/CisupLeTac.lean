import Mathlib

/-- Reduces `⨆ i, f i ≤ c` to `f i ≤ c` and introduces the index variable.
    Tries `ciSup_le` first (the unconditional form), then falls back to
    `ciSup_le_iff` with a `BddAbove` side-goal discharged by `assumption`. -/
macro "ciSup_le_tac" : tactic =>
  `(tactic| first
    | (apply ciSup_le; intro)
    | (refine (ciSup_le_iff ?_).mpr ?_; · assumption; · intro))
