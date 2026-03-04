import Mathlib

/-- `sum_nonneg_search` proves goals of the form `0 ≤ ∑ i ∈ s, f i`
    (especially over `Ico`/`range`/`Icc` intervals) by applying
    `Finset.sum_nonneg`, introducing the index and membership hypothesis,
    simplifying Ico/range/Icc membership to arithmetic bounds, and then
    closing the nonnegativity subgoal via `linarith`, `positivity`,
    `assumption`, or `solve_by_elim`. -/
macro "sum_nonneg_search" : tactic =>
  `(tactic| (apply Finset.sum_nonneg;
             intro _sum_idx _sum_mem;
             simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_Icc,
                        Finset.mem_insert, Finset.mem_singleton] at _sum_mem;
             first
             | linarith
             | positivity
             | assumption
             | solve_by_elim))
