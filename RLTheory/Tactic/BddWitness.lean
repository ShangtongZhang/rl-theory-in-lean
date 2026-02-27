import Mathlib

/-- For goals of the form `∃ C, 0 ≤ C ∧ P C`, accepts an explicit witness term,
    introduces it, and automatically discharges the nonnegativity obligation using
    `positivity`, leaving only `P C` as the remaining goal. --/
macro "bdd_witness" t:term : tactic =>
  `(tactic| (refine ⟨$t, ?bdd_nonneg__, ?_⟩; case bdd_nonneg__ => positivity))
