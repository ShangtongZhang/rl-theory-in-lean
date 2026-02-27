import Mathlib

/-- For goals of the form `∃ C, 0 ≤ C ∧ P C`, accepts a term `e` for `C`,
    provides `e` as the witness, automatically discharges the nonnegativity
    side-condition `0 ≤ e` via `norm_num`, `positivity`, or `linarith`,
    and leaves only `P e` as the remaining goal. --/
macro "nonneg_exists_intro" e:term : tactic =>
  `(tactic| (refine ⟨$e, ?_, ?_⟩
             · first | norm_num | positivity | linarith))
