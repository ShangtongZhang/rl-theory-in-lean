import Mathlib
import RLTheory.Tactic.ExistsBoundNonneg

-- Demonstrate `exists_bound_nonneg` on a concrete goal: find a nonneg bound C
-- such that C ≥ 2, using 3 as the witness (nonnegativity discharged automatically).
example : ∃ C : ℝ, 0 ≤ C ∧ C ≥ 2 := by
  exists_bound_nonneg 3
  norm_num
