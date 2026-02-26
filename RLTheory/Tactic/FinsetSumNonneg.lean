import Mathlib

/-- Closes goals of the form `0 ≤ ∑ i ∈ s, f i` by applying `Finset.sum_nonneg`,
    simplifying membership predicates, and dispatching per-element nonnegativity
    via `linarith` or `positivity`.
    Optionally accepts a custom tactic block via `using <tactic>`. --/
macro "finset_sum_nonneg" : tactic =>
  `(tactic| (
      apply Finset.sum_nonneg
      intro _i _hi
      simp only [Finset.mem_Ico, Finset.mem_range] at _hi
      first | linarith | positivity))

macro "finset_sum_nonneg" "using" t:tactic : tactic =>
  `(tactic| (
      apply Finset.sum_nonneg
      intro _i _hi
      simp only [Finset.mem_Ico, Finset.mem_range] at _hi
      $t))
