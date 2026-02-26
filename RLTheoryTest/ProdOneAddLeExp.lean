import Mathlib
import RLTheory.Tactic.ProdOneAddLeExp

-- one example that uses `prod_one_add_le_exp` as a proof step
example (s : Finset ℕ) :
    ∏ i ∈ s, (1 + (i : ℝ)) ≤ Real.exp (∑ i ∈ s, (i : ℝ)) := by
  prod_one_add_le_exp
