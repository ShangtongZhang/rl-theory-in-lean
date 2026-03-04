import Mathlib
import RLTheory.Tactic.IcoProdSumSimp

-- Demonstrate that `Ico_prod_sum_simp` can rewrite exp of a sum over an Ico
-- interval into a product of exponentials over the same interval.
open Real Finset in
example (n : ℕ) (c : ℕ → ℝ) :
    exp (∑ i ∈ Ico 0 n, c i) = ∏ i ∈ Ico 0 n, exp (c i) := by
  Ico_prod_sum_simp
