import Mathlib

/-- For goals of the form `∃ C, 0 ≤ C ∧ P C`, accepts a term `e` for `C`,
    provides `e` as the witness, and automatically discharges the nonnegativity
    side-condition `0 ≤ e` via `positivity` (falling back to `linarith` then
    `norm_num`), leaving only `P e` as the remaining goal. --/
macro "exists_bound_nonneg" e:term : tactic =>
  `(tactic| (refine ⟨$e, ?_, ?_⟩
             · first | positivity | linarith | norm_num))
