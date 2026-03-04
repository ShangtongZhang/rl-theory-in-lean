import Mathlib
import RLTheory.Tactic.ProdPosIco

-- Demonstrate `prod_pos_Ico` on a product over a Finset.Ico interval
-- where each factor is (1 + i) for i : ℕ cast to ℝ.
example (n : ℕ) : 0 < ∏ i ∈ Finset.Ico 0 n, (1 + (i : ℝ)) := by
  prod_pos_Ico
