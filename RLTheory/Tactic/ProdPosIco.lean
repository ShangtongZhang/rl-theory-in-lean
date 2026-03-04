import Mathlib

/-- `prod_pos_Ico` proves `0 < ∏ i ∈ s, f i` (typically over a `Finset.Ico`
    interval) by applying `Finset.prod_pos`, simplifying membership to
    arithmetic bounds, and closing each factor's positivity subgoal with
    `linarith` or `positivity`. -/
macro "prod_pos_Ico" : tactic =>
  `(tactic| (
    apply Finset.prod_pos
    intro _prod_idx _prod_mem
    simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_Icc] at _prod_mem
    first
    | linarith
    | positivity
    | (apply add_pos_of_pos_of_nonneg
       · linarith
       · positivity)
    | (apply add_pos_of_nonneg_of_pos
       · positivity
       · linarith)
    | (apply add_pos_of_pos_of_nonneg <;> linarith)
    | (apply add_pos_of_nonneg_of_pos <;> linarith)
  ))
