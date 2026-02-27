import Mathlib

/-- Closes goals of the form `∑ i ∈ Ico a b, f i ≤ ∑ i ∈ Ico a c, f i` (or `range` variants)
    when `b ≤ c` and `f` is nonneg, by applying `Finset.sum_le_sum_of_subset` or
    `Finset.sum_le_sum_of_subset_of_nonneg` with subset membership discharged by `omega`,
    and nonnegativity discharged by `positivity` or `linarith`. --/
macro "nonneg_sum_mono_le" : tactic =>
  `(tactic| (
      first
      | (apply Finset.sum_le_sum_of_subset
         · intro i hi
           simp only [Finset.mem_Ico, Finset.mem_range] at *
           omega)
      | (apply Finset.sum_le_sum_of_subset_of_nonneg
         · intro i hi
           simp only [Finset.mem_Ico, Finset.mem_range] at *
           omega
         · intro i _ _
           first | positivity | linarith)
      | (apply Finset.single_le_sum
         · intro i _; positivity
         · simp)))
