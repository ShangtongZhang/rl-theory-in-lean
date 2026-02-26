import Mathlib

/-- Closes goals of the form `∏ i ∈ s, (1 + f i) ≤ exp (∑ i ∈ s, f i)` by rewriting
    the RHS via `exp_sum`, applying `Finset.prod_le_prod` per element,
    using `Real.add_one_le_exp` for the upper-bound side-goal, and discharging
    nonnegativity side-goals via `linarith` or `positivity`. --/
macro "prod_one_add_le_exp" : tactic =>
  `(tactic| (
      rw [Real.exp_sum]
      apply Finset.prod_le_prod
      · intro i _hi
        simp only [Finset.mem_Ico, Finset.mem_range] at _hi
        apply add_nonneg
        · norm_num
        · first | linarith | positivity
      · intro i _hi
        simp only [Finset.mem_Ico, Finset.mem_range] at _hi
        rw [add_comm]
        exact Real.add_one_le_exp _))
